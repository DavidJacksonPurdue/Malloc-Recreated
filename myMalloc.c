#include <errno.h>
#include <pthread.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "myMalloc.h"
#include "printing.h"

/* Due to the way assert() prints error messges we use out own assert function
 * for deteminism when testing assertions
 */
#ifdef TEST_ASSERT
  inline static void assert(int e) {
    if (!e) {
      const char * msg = "Assertion Failed!\n";
      write(2, msg, strlen(msg));
      exit(1);
    }
  }
#else
  #include <assert.h>
#endif

/*
 * Mutex to ensure thread safety for the freelist
 */
static pthread_mutex_t mutex;

/*
 * Array of sentinel nodes for the freelists
 */
header freelistSentinels[N_LISTS];

/*
 * Pointer to the second fencepost in the most recently allocated chunk from
 * the OS. Used for coalescing chunks
 */
header * lastFencePost;

/*
 * Pointer to maintian the base of the heap to allow printing based on the
 * distance from the base of the heap
 */ 
void * base;

/*
 * List of chunks allocated by  the OS for printing boundary tags
 */
header * osChunkList [MAX_OS_CHUNKS];
size_t numOsChunks = 0;

/*
 * direct the compiler to run the init function before running main
 * this allows initialization of required globals
 */
static void init (void) __attribute__ ((constructor));

// Helper functions for manipulating pointers to headers
static inline header * get_header_from_offset(void * ptr, ptrdiff_t off);
static inline header * get_left_header(header * h);
static inline header * ptr_to_header(void * p);

// Helper functions for allocating more memory from the OS
static inline void initialize_fencepost(header * fp, size_t left_size);
static inline void insert_os_chunk(header * hdr);
static inline void insert_fenceposts(void * raw_mem, size_t size);
static header * allocate_chunk(size_t size);

// Helper functions for freeing a block
static inline void deallocate_object(void * p);

// Helper functions for allocating a block
static inline header * allocate_object(size_t raw_size);

// Helper functions for verifying that the data structures are structurally 
// valid
static inline header * detect_cycles();
static inline header * verify_pointers();
static inline bool verify_freelist();
static inline header * verify_chunk(header * chunk);
static inline bool verify_tags();

static void init();

static bool isMallocInitialized;

/**
 * @brief Helper function to retrieve a header pointer from a pointer and an 
 *        offset
 *
 * @param ptr base pointer
 * @param off number of bytes from base pointer where header is located
 *
 * @return a pointer to a header offset bytes from pointer
 */
static inline header * get_header_from_offset(void * ptr, ptrdiff_t off) {
	return (header *)((char *) ptr + off);
}

/**
 * @brief Helper function to get the header to the right of a given header
 *
 * @param h original header
 *
 * @return header to the right of h
 */
header * get_right_header(header * h) {
	return get_header_from_offset(h, get_block_size(h));
}

/**
 * @brief Helper function to get the header to the left of a given header
 *
 * @param h original header
 *
 * @return header to the right of h
 */
inline static header * get_left_header(header * h) {
  return get_header_from_offset(h, -h->left_size);
}

/**
 * @brief Fenceposts are marked as always allocated and may need to have
 * a left object size to ensure coalescing happens properly
 *
 * @param fp a pointer to the header being used as a fencepost
 * @param left_size the size of the object to the left of the fencepost
 */
inline static void initialize_fencepost(header * fp, size_t left_size) {
	set_block_state(fp,FENCEPOST);
	set_block_size(fp, ALLOC_HEADER_SIZE);
	fp->left_size = left_size;
}

/**
 * @brief Helper function to maintain list of chunks from the OS for debugging
 *
 * @param hdr the first fencepost in the chunk allocated by the OS
 */
inline static void insert_os_chunk(header * hdr) {
  if (numOsChunks < MAX_OS_CHUNKS) {
    osChunkList[numOsChunks++] = hdr;
  }
}

/**
 * @brief given a chunk of memory insert fenceposts at the left and 
 * right boundaries of the block to prevent coalescing outside of the
 * block
 *
 * @param raw_mem a void pointer to the memory chunk to initialize
 * @param size the size of the allocated chunk
 */
inline static void insert_fenceposts(void * raw_mem, size_t size) {
  // Convert to char * before performing operations
  char * mem = (char *) raw_mem;

  // Insert a fencepost at the left edge of the block
  header * leftFencePost = (header *) mem;
  initialize_fencepost(leftFencePost, ALLOC_HEADER_SIZE);

  // Insert a fencepost at the right edge of the block
  header * rightFencePost = get_header_from_offset(mem, size - ALLOC_HEADER_SIZE);
  initialize_fencepost(rightFencePost, size - 2 * ALLOC_HEADER_SIZE);
}

/**
 * @brief Allocate another chunk from the OS and prepare to insert it
 * into the free list
 *
 * @param size The size to allocate from the OS
 *
 * @return A pointer to the allocable block in the chunk (just after the 
 * first fencpost)
 */
static header * allocate_chunk(size_t size) {
  void * mem = sbrk(size);
  insert_fenceposts(mem, size);
  header * hdr = (header *) ((char *)mem + ALLOC_HEADER_SIZE);
  set_block_state(hdr, UNALLOCATED);
  set_block_size(hdr, size - 2 * ALLOC_HEADER_SIZE);
  hdr->left_size = ALLOC_HEADER_SIZE;
  return hdr;
}

/**
 * @brief Helper allocate an object given a raw request size from the user
 *
 * @param raw_size number of bytes the user needs
 *
 * @return A block satisfying the user's request
 */
static inline header * allocate_object(size_t raw_size) {
  if (raw_size == 0) {
    return NULL;
  }
  int freelist_index = 1;
  int rounded_size = 16;

  //MIN_ALLOCATION = 8. Alloc data needs 16 raw as room for pointers
  if (raw_size > 2 * MIN_ALLOCATION) {
    freelist_index = (raw_size - 1) / 8;
    if (freelist_index >= N_LISTS - 1) {
      freelist_index = N_LISTS - 1;
    }
    if (raw_size % 8 != 0) {
      rounded_size = raw_size + (8 - (raw_size % 8));
    }
    else {
      rounded_size = raw_size;
    }
  }
  for (int i = freelist_index; i < N_LISTS; i++) {
    header *cur_header = &freelistSentinels[i];
    if (i != N_LISTS - 1) {
      if (cur_header->next != cur_header) {
        cur_header = cur_header->next;
        if (get_block_size(cur_header) - ALLOC_HEADER_SIZE - rounded_size >= sizeof(header)) {
        //If there is enough space for another header in the block 0when excluding the 16
        //bytes taken up by next and prev and the requested size, split the block
          header *right_header = get_right_header(cur_header);
          right_header->left_size = rounded_size + ALLOC_HEADER_SIZE;
          header *new_header = get_header_from_offset(right_header, -(rounded_size + ALLOC_HEADER_SIZE));
          set_block_size(cur_header, get_block_size(cur_header) - ALLOC_HEADER_SIZE - rounded_size);
          new_header->left_size = get_block_size(cur_header);
          set_block_state(new_header, ALLOCATED);
          set_block_size(new_header, rounded_size + ALLOC_HEADER_SIZE);
          cur_header->prev->next = cur_header->next;
          cur_header->next->prev = cur_header->prev;
          cur_header->next = NULL;
          cur_header->prev = NULL;
          int new_header_loc = (get_block_size(cur_header) - ALLOC_HEADER_SIZE - 1) / 8;
          cur_header->next = freelistSentinels[new_header_loc].next;
          cur_header->next->prev = cur_header;
          freelistSentinels[new_header_loc].next = cur_header;
          cur_header->prev = &freelistSentinels[new_header_loc];
          return (header *) new_header->data;
        }
        else {
          cur_header->prev->next = cur_header->next;
          cur_header->next->prev = cur_header->prev;
          cur_header->next = NULL;
          cur_header->prev = NULL;
          set_block_state(cur_header, ALLOCATED);
          return (header *) cur_header->data;
        }
      }
    }
    else {
      cur_header = cur_header->next;
      while (cur_header != &freelistSentinels[N_LISTS - 1]) {
        if (get_block_size(cur_header) - ALLOC_HEADER_SIZE >= rounded_size) {
          if (get_block_size(cur_header) - ALLOC_HEADER_SIZE - rounded_size >= sizeof(header)) {
          //Split from list of any size
            header *right_header = get_right_header(cur_header);
            right_header->left_size = rounded_size + ALLOC_HEADER_SIZE;
            header *new_header = get_header_from_offset(right_header, -(rounded_size + ALLOC_HEADER_SIZE));
            set_block_size(cur_header, get_block_size(cur_header) - rounded_size - ALLOC_HEADER_SIZE);
            new_header->left_size = get_block_size(cur_header);
            set_block_state(new_header, ALLOCATED);
            set_block_size(new_header, rounded_size + ALLOC_HEADER_SIZE);
            int new_header_loc = (get_block_size(cur_header) - ALLOC_HEADER_SIZE - 1) / 8;
            if (new_header_loc < N_LISTS - 1) {
              cur_header->prev->next = cur_header->next;
              cur_header->next->prev = cur_header->prev;
              cur_header->next = NULL;
              cur_header->prev = NULL;
              cur_header->next = freelistSentinels[new_header_loc].next;
              cur_header->next->prev = cur_header;
              freelistSentinels[new_header_loc].next = cur_header;
              cur_header->prev = &freelistSentinels[new_header_loc];
            }
            return (header *) new_header->data;
          }
          else {
          //near exact match found
            cur_header->prev->next = cur_header->next;
            cur_header->next->prev = cur_header->prev;
            cur_header->prev = NULL;
            cur_header->next = NULL;
            set_block_state(cur_header, ALLOCATED);
            return (header *) cur_header->data;
          }
        }
        else {
          cur_header = cur_header->next;
        }
      }
    }
  }
  //Here is where you need to handle case of allocating extra block
  header *block = allocate_chunk(ARENA_SIZE);
  if (block == NULL) {
    return NULL;
  }
  header *new_left_fencepost = get_header_from_offset(block, -(ALLOC_HEADER_SIZE));
  header *new_right_fencepost = get_header_from_offset(block, get_block_size(block));
  if (lastFencePost == get_header_from_offset(new_left_fencepost, -(ALLOC_HEADER_SIZE))) {
  //if condition is met, then chunks are consecutive and need to be coalesced
    header *old_right_header = get_left_header(lastFencePost);
    if (get_block_state(old_right_header) == UNALLOCATED) {
    //If the old rightmost is unallocated, we need to coalesce fenceposts, new block, and old
      old_right_header->next->prev = old_right_header->prev;
      old_right_header->prev->next = old_right_header->next;
      old_right_header->prev = NULL;
      old_right_header->next = NULL;
      set_block_state(new_left_fencepost, UNALLOCATED);
      set_block_state(lastFencePost, UNALLOCATED);
      size_t temp_size = get_block_size(block);
      block = old_right_header;
      set_block_size(block, temp_size + 2 * ALLOC_HEADER_SIZE + get_block_size(old_right_header));
      header *even_lefter_header = get_left_header(old_right_header);
      block->left_size = get_block_size(even_lefter_header);
      new_right_fencepost->left_size = get_block_size(block);
      lastFencePost = new_right_fencepost;
      //Now new block needs to be inserted into freelist
      block->next = freelistSentinels[N_LISTS - 1].next;
      block->next->prev = block;
      freelistSentinels[N_LISTS - 1].next = block;
      block->prev = &freelistSentinels[N_LISTS - 1];
      return allocate_object(raw_size);
    }
    else {
    //Otherwise, only the fenceposts and new block need to be coalesced
      set_block_state(new_left_fencepost, UNALLOCATED);
      size_t temp_size = get_block_size(block);
      block = lastFencePost;
      set_block_state(block, UNALLOCATED);
      set_block_size(block, temp_size + 2 * ALLOC_HEADER_SIZE);
      block->left_size = get_block_size(old_right_header);
      new_right_fencepost->left_size = get_block_size(block);
      lastFencePost = new_right_fencepost;
      //Now we need to insert new block into freelist
      block->next = freelistSentinels[N_LISTS - 1].next;
      block->next->prev = block;
      freelistSentinels[N_LISTS - 1].next = block;
      block->prev = &freelistSentinels[N_LISTS - 1];
      return allocate_object(raw_size);
    }
  }
  else {
  //if condition is not met, then chunks are not consecutive, so no coalescing is needed.
    insert_os_chunk(new_left_fencepost);
    lastFencePost = new_right_fencepost;
    block->next = freelistSentinels[N_LISTS - 1].next;
    block->next->prev = block;
    freelistSentinels[N_LISTS - 1].next = block;
    block->prev = &freelistSentinels[N_LISTS - 1];
    return allocate_object(raw_size);
  }
}

/**
 * @brief Helper to get the header from a pointer allocated with malloc
 *
 * @param p pointer to the data region of the block
 *
 * @return A pointer to the header of the block
 */
static inline header * ptr_to_header(void * p) {
  return (header *)((char *) p - ALLOC_HEADER_SIZE); //sizeof(header));
}

/**
 * @brief Helper to manage deallocation of a pointer returned by the user
 *
 * @param p The pointer returned to the user by a call to malloc
 */
static inline void deallocate_object(void * p) {
  if (p == NULL) {
  //Freeing a null pointer should do nothing
    return;
  }
  header *cur_header = ptr_to_header(p);
  if (get_block_state(cur_header) == UNALLOCATED) {
  //Only allocated blocks can be freed
    printf("Double Free Detected\n");
    fflush(stdout);
    assert(0);
    return;
  }
  if (get_block_state(cur_header) == FENCEPOST) {
    return;
  }
  header *right_header = get_right_header(cur_header);
  header *left_header = get_left_header(cur_header);
  set_block_state(cur_header, UNALLOCATED);
  if (get_block_state(left_header) != UNALLOCATED && get_block_state(right_header) != UNALLOCATED) {
  //If both left and right blocks are allocated, then no coalescing occurs
    int new_header_loc = (get_block_size(cur_header) - ALLOC_HEADER_SIZE - 1) / 8;
    if (new_header_loc >= N_LISTS - 1) {
      new_header_loc = N_LISTS - 1;
    }
    cur_header->next = freelistSentinels[new_header_loc].next;
    cur_header->next->prev = cur_header;
    freelistSentinels[new_header_loc].next = cur_header;
    cur_header->prev = &freelistSentinels[new_header_loc];
  }
  else if (get_block_state(left_header) != UNALLOCATED && get_block_state(right_header) == UNALLOCATED) {
  //If right is free, but left is not, only coalesce right. cur_header becomes bigger.
    int right_header_loc = (get_block_size(right_header) - ALLOC_HEADER_SIZE - 1) / 8;
    if (right_header_loc >= N_LISTS - 1) {
      right_header_loc = N_LISTS - 1;
    }
    header *even_righter = get_right_header(right_header);
    set_block_size(cur_header, get_block_size(cur_header) + get_block_size(right_header));
    even_righter->left_size = get_block_size(cur_header);
    int new_header_loc = (get_block_size(cur_header) - ALLOC_HEADER_SIZE - 1) / 8;
    if (new_header_loc >= N_LISTS - 1) {
      new_header_loc = N_LISTS - 1;
    }
    if (right_header_loc == new_header_loc) {
      right_header->next->prev = cur_header;
      right_header->prev->next = cur_header;
      cur_header->next = right_header->next;
      cur_header->prev = right_header->prev;
      right_header->next = NULL;
      right_header->prev = NULL;
      return;
    }
    //This is adding coalesced cur_header to free list
    cur_header->next = freelistSentinels[new_header_loc].next;
    cur_header->next->prev = cur_header;
    freelistSentinels[new_header_loc].next = cur_header;
    cur_header->prev = &freelistSentinels[new_header_loc];
    //This is removing right_header from free list
    right_header->next->prev = right_header->prev;
    right_header->prev->next = right_header->next;
    right_header->prev = NULL;
    right_header->next = NULL;
  }
  else if (get_block_state(left_header) == UNALLOCATED && get_block_state(right_header) != UNALLOCATED) {
  //If left is free, but right is not, only coalesce left. cur header is replaced by left header
    int left_header_loc = (get_block_size(left_header) - ALLOC_HEADER_SIZE - 1) / 8;
    if (left_header_loc >= N_LISTS - 1) {
      left_header_loc = N_LISTS - 1;
    }
    set_block_size(left_header, get_block_size(left_header) + get_block_size(cur_header));
    right_header->left_size = get_block_size(left_header);
    int new_header_loc = (get_block_size(left_header) - ALLOC_HEADER_SIZE - 1) / 8;
    if (new_header_loc >= N_LISTS - 1) {
      new_header_loc = N_LISTS - 1;
    }
    if (left_header_loc == new_header_loc) {
    //If the left header would end up in the same index of the freelist, there is no need to move it
      return;
    }
    //This is adding coalesce left_header to free list and removing it from its old spot
    left_header->next->prev = left_header->prev;
    left_header->prev->next = left_header->next;
    left_header->prev = NULL;
    left_header->next = NULL;
    left_header->next = freelistSentinels[new_header_loc].next;
    left_header->next->prev = left_header;
    freelistSentinels[new_header_loc].next = left_header;
    left_header->prev = &freelistSentinels[new_header_loc];
  }
  else {
  //In the instance left is free and right is free, both must be coalesced
    int left_header_loc = (get_block_size(left_header) - ALLOC_HEADER_SIZE - 1) / 8;
    if (left_header_loc >= N_LISTS - 1) {
      left_header_loc = N_LISTS - 1;
    }
    header *even_righter = get_right_header(right_header);
    set_block_size(left_header, get_block_size(left_header) + get_block_size(cur_header) + get_block_size(right_header));
    even_righter->left_size = get_block_size(left_header);
    int new_header_loc = (get_block_size(left_header) - ALLOC_HEADER_SIZE - 1) / 8;
    if (new_header_loc >= N_LISTS - 1) {
      new_header_loc = N_LISTS - 1;
    }
    if (left_header_loc == new_header_loc) {
    //This is removing right_header from free list
      right_header->next->prev = right_header->prev;
      right_header->prev->next = right_header->next;
      right_header->prev= NULL;
      right_header->next = NULL;
      return;
    }
    //This is adding coalesced left_header to free list and removing it from its old spot
    left_header->next->prev = left_header->prev;
    left_header->prev->next = left_header->next;
    left_header->prev = NULL;
    left_header->next = NULL;
    left_header->next = freelistSentinels[new_header_loc].next;
    left_header->next->prev = left_header;
    freelistSentinels[new_header_loc].next = left_header;
    left_header->prev = &freelistSentinels[new_header_loc];
    //This is removing right_header from free list  
    right_header->next->prev = right_header->prev;
    right_header->prev->next = right_header->next;
    right_header->prev = NULL;
    right_header->next = NULL;
  }
}

/**
 * @brief Helper to detect cycles in the free list
 * https://en.wikipedia.org/wiki/Cycle_detection#Floyd's_Tortoise_and_Hare
 *
 * @return One of the nodes in the cycle or NULL if no cycle is present
 */
static inline header * detect_cycles() {
  for (int i = 0; i < N_LISTS; i++) {
    header * freelist = &freelistSentinels[i];
    for (header * slow = freelist->next, * fast = freelist->next->next; 
         fast != freelist; 
         slow = slow->next, fast = fast->next->next) {
      if (slow == fast) {
        return slow;
      }
    }
  }
  return NULL;
}

/**
 * @brief Helper to verify that there are no unlinked previous or next pointers
 *        in the free list
 *
 * @return A node whose previous and next pointers are incorrect or NULL if no
 *         such node exists
 */
static inline header * verify_pointers() {
  for (int i = 0; i < N_LISTS; i++) {
    header * freelist = &freelistSentinels[i];
    for (header * cur = freelist->next; cur != freelist; cur = cur->next) {
      if (cur->next->prev != cur || cur->prev->next != cur) {
        return cur;
      }
    }
  }
  return NULL;
}

/**
 * @brief Verify the structure of the free list is correct by checkin for 
 *        cycles and misdirected pointers
 *
 * @return true if the list is valid
 */
static inline bool verify_freelist() {
  header * cycle = detect_cycles();
  if (cycle != NULL) {
    fprintf(stderr, "Cycle Detected\n");
    print_sublist(print_object, cycle->next, cycle);
    return false;
  }

  header * invalid = verify_pointers();
  if (invalid != NULL) {
    fprintf(stderr, "Invalid pointers\n");
    print_object(invalid);
    return false;
  }

  return true;
}

/**
 * @brief Helper to verify that the sizes in a chunk from the OS are correct
 *        and that allocated node's canary values are correct
 *
 * @param chunk AREA_SIZE chunk allocated from the OS
 *
 * @return a pointer to an invalid header or NULL if all header's are valid
 */
static inline header * verify_chunk(header * chunk) {
	if (get_block_state(chunk) != FENCEPOST) {
		fprintf(stderr, "Invalid fencepost\n");
		print_object(chunk);
		return chunk;
	}
	
	for (; get_block_state(chunk) != FENCEPOST; chunk = get_right_header(chunk)) {
		if (get_block_size(chunk)  != get_right_header(chunk)->left_size) {
			fprintf(stderr, "Invalid sizes\n");
			print_object(chunk);
			return chunk;
		}
	}
	
	return NULL;
}

/**
 * @brief For each chunk allocated by the OS verify that the boundary tags
 *        are consistent
 *
 * @return true if the boundary tags are valid
 */
static inline bool verify_tags() {
  for (size_t i = 0; i < numOsChunks; i++) {
    header * invalid = verify_chunk(osChunkList[i]);
    if (invalid != NULL) {
      return invalid;
    }
  }

  return NULL;
}

/**
 * @brief Initialize mutex lock and prepare an initial chunk of memory for allocation
 */
static void init() {
  // Initialize mutex for thread safety
  pthread_mutex_init(&mutex, NULL);

#ifdef DEBUG
  // Manually set printf buffer so it won't call malloc when debugging the allocator
  setvbuf(stdout, NULL, _IONBF, 0);
#endif // DEBUG

  // Allocate the first chunk from the OS
  header * block = allocate_chunk(ARENA_SIZE);

  header * prevFencePost = get_header_from_offset(block, -ALLOC_HEADER_SIZE);
  insert_os_chunk(prevFencePost);

  lastFencePost = get_header_from_offset(block, get_block_size(block));

  // Set the base pointer to the beginning of the first fencepost in the first
  // chunk from the OS
  base = ((char *) block) - ALLOC_HEADER_SIZE; //sizeof(header);

  // Initialize freelist sentinels
  for (int i = 0; i < N_LISTS; i++) {
    header * freelist = &freelistSentinels[i];
    freelist->next = freelist;
    freelist->prev = freelist;
  }

  // Insert first chunk into the free list
  header * freelist = &freelistSentinels[N_LISTS - 1];
  freelist->next = block;
  freelist->prev = block;
  block->next = freelist;
  block->prev = freelist;
}

/* 
 * External interface
 */
void * my_malloc(size_t size) {
  pthread_mutex_lock(&mutex);
  header * hdr = allocate_object(size); 
  pthread_mutex_unlock(&mutex);
  return hdr;
}

void * my_calloc(size_t nmemb, size_t size) {
  return memset(my_malloc(size * nmemb), 0, size * nmemb);
}

void * my_realloc(void * ptr, size_t size) {
  void * mem = my_malloc(size);
  memcpy(mem, ptr, size);
  my_free(ptr);
  return mem;
}

void my_free(void * p) {
  pthread_mutex_lock(&mutex);
  deallocate_object(p);
  pthread_mutex_unlock(&mutex);
}

bool verify() {
  return verify_freelist() && verify_tags();
}
