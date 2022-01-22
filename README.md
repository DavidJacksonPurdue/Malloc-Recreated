This is a recreation of the c malloc library functions (including calloc) written from the ground up in C. This recreation is functionally identical and was made to demonstrate
knowledge of dynamic memory allocation. It includes fenceposts (for seperation of memory blocks), it maintains freelists for quick allocation of fitting data, it automatically
rounds allocated memory to the nearest 8 bytes, and the minimum allocated memory must be at least 16 (8 bytes for memory, and 8 bytes are needed for pointers to maintain freelist).
