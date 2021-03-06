/**************************************************************************/
/*                                                                        */
/*  This file is part of the Frama-C's E-ACSL plug-in.                    */
/*                                                                        */
/*  Copyright (C) 2012-2014                                               */
/*    CEA (Commissariat � l'�nergie atomique et aux �nergies              */
/*         alternatives)                                                  */
/*                                                                        */
/*  you can redistribute it and/or modify it under the terms of the GNU   */
/*  Lesser General Public License as published by the Free Software       */
/*  Foundation, version 2.1.                                              */
/*                                                                        */
/*  It is distributed in the hope that it will be useful,                 */
/*  but WITHOUT ANY WARRANTY; without even the implied warranty of        */
/*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the         */
/*  GNU Lesser General Public License for more details.                   */
/*                                                                        */
/*  See the GNU Lesser General Public License version 2.1                 */
/*  for more details (enclosed in the file licenses/LGPLv2.1).            */
/*                                                                        */
/**************************************************************************/

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>
#include <assert.h>
#include "e_acsl_mmodel_api.h"
#include "e_acsl_mmodel.h"


#define WARNING 0
#define ERROR 1
#define IGNORE 2


#ifdef E_ACSL_WARNING
int __warning_level = E_ACSL_WARNING;
#else
int __warning_level = WARNING;
#endif


void __warning(const char* fct_name) {
  fprintf(stderr,
	  "warning: E_ACSL function '%s' called with null pointer\n", fct_name);
}


void* __e_acsl_memset (void* dest, int val, size_t len) {
  unsigned char *ptr = (unsigned char*)dest;
  while (len-- > 0)
    *ptr++ = val;
  return dest;
}


size_t __memory_size = 0;
/*unsigned cpt_store_block = 0;*/

const int nbr_bits_to_1[256] = {
  0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4,1,2,2,3,2,3,3,4,2,3,3,4,3,4,4,5,1,2,2,3,2,3,3,4,2,3,3,4,3,4,4,5,2,3,3,4,3,4,4,5,3,4,4,5,4,5,5,6,1,2,2,3,2,3,3,4,2,3,3,4,3,4,4,5,2,3,3,4,3,4,4,5,3,4,4,5,4,5,5,6,2,3,3,4,3,4,4,5,3,4,4,5,4,5,5,6,3,4,4,5,4,5,5,6,4,5,5,6,5,6,6,7,1,2,2,3,2,3,3,4,2,3,3,4,3,4,4,5,2,3,3,4,3,4,4,5,3,4,4,5,4,5,5,6,2,3,3,4,3,4,4,5,3,4,4,5,4,5,5,6,3,4,4,5,4,5,5,6,4,5,5,6,5,6,6,7,2,3,3,4,3,4,4,5,3,4,4,5,4,5,5,6,3,4,4,5,4,5,5,6,4,5,5,6,5,6,6,7,3,4,4,5,4,5,5,6,4,5,5,6,5,6,6,7,4,5,5,6,5,6,6,7,5,6,6,7,6,7,7,8
};

/*@ assigns \nothing;
  @ ensures \result == __memory_size;
  @*/
size_t __get_memory_size(void) {
  return __memory_size;
}

/*@ assigns \nothing;
  @ ensures size%8 == 0 ==> \result == size/8;
  @ ensures size%8 != 0 ==> \result == size/8+1;
  @*/
size_t needed_bytes (size_t size) {
  return (size % 8) == 0 ? (size/8) : (size/8 + 1);
}

/* store the block of size bytes starting at ptr */
void* __store_block(void* ptr, size_t size) {
  struct _block * tmp;
  assert(ptr != NULL);
  tmp = malloc(sizeof(struct _block));
  assert(tmp != NULL);
  tmp->ptr = (size_t)ptr;
  tmp->size = size;
  tmp->init_ptr = NULL;
  tmp->init_cpt = 0;
  tmp->is_litteral_string = false;
  tmp->is_out_of_bound = false;
  __add_element(tmp);
  /*cpt_store_block++;*/
  return ptr;
}

/* remove the block starting at ptr */
void __delete_block(void* ptr) {
  struct _block * tmp;
  assert(ptr != NULL);
  tmp = __get_exact(ptr);
  assert(tmp != NULL);
  __clean_init(tmp);
  __remove_element(tmp);
  free(tmp);
}

/* allocate size bytes and store the returned block
 * for further information, see malloc */
void* __malloc(size_t size) {
  void * tmp, * tmp2;
  if(size <= 0) return NULL;
  tmp = malloc(size);
  if(tmp == NULL) return NULL;
  tmp2 = __store_block(tmp, size);
  __memory_size += size;
  assert(tmp2 != NULL);
  return tmp2;
}

/* free the block starting at ptr,
 * for further information, see free */
void __free(void* ptr) {
  struct _block * tmp;
  if(ptr == NULL) return;
  tmp = __get_exact(ptr);
  assert(tmp != NULL);
  free(ptr);
  __clean_init(tmp);
  __memory_size -= tmp->size;
  __remove_element(tmp);
  free(tmp);
}

/* resize the block starting at ptr to fit its new size,
 * for further information, see realloc */
void* __realloc(void* ptr, size_t size) {
  struct _block * tmp;
  void * new_ptr;
  if(ptr == NULL) return __malloc(size);
  if(size <= 0) {
    __memory_size -= __get_exact(ptr)->size;
    __free(ptr);
    return NULL;
  }
  tmp = __get_exact(ptr);
  __memory_size -= tmp->size;
  assert(tmp != NULL);
  new_ptr = realloc((void*)tmp->ptr, size);
  if(new_ptr == NULL) return NULL;
  tmp->ptr = (size_t)new_ptr;
  /* uninitialized, do nothing */
  if(tmp->init_cpt == 0) ;
  /* already fully initialized block */
  else if (tmp->init_cpt == tmp->size) {
    /* realloc smaller block */
    if(size <= tmp->size)
      /* adjust new size, allocation not necessary */
      tmp->init_cpt = size;
    /* realloc bigger larger block */
    else {
      int nb = needed_bytes(size);
      tmp->init_ptr = malloc(nb);
      __e_acsl_memset(tmp->init_ptr, 0xFF, nb);
      if(size%8 != 0)
	tmp->init_ptr[size/8] <<= (8 - size%8);
    }
  }
  /* contains initialized and uninitialized parts */
  else {
    int nb = needed_bytes(size);
    int nb_old = needed_bytes(tmp->size);
    int i;
    tmp->init_ptr = realloc(tmp->init_ptr, nb);
    for(i = nb_old; i < nb; i++)
      tmp->init_ptr[i] = 0;
    tmp->init_cpt = 0;
    for(i = 0; i < nb; i++)
      tmp->init_cpt += nbr_bits_to_1[tmp->init_ptr[i]];
    if(tmp->init_cpt == size || tmp->init_cpt == 0) {
      free(tmp->init_ptr);
      tmp->init_ptr = NULL;
    }
  }
  tmp->size = size;
  __memory_size += size;
  return (void*)tmp->ptr;
}

/* allocate memory for an array of nbr_block elements of size_block size,
 * this memory is set to zero, the returned block is stored,
 * for further information, see calloc */
void* __calloc(size_t nbr_block, size_t size_block) {
  void * tmp, * tmp2;
  if(nbr_block * size_block <= 0) return NULL;
  tmp = calloc(nbr_block, size_block);
  if(tmp == NULL) return NULL;
  tmp2 = __store_block(tmp, nbr_block * size_block);
  __memory_size += nbr_block * size_block;
  assert(tmp2 != NULL);
  return tmp2;
}

/* mark the size bytes of ptr as initialized */
void __initialize (void * ptr, size_t size) {
  struct _block * tmp;
  unsigned i;

  if(ptr == NULL) {
    if(__warning_level == ERROR) assert(0);
    else if(__warning_level == IGNORE) return;
    else { __warning("initialize"); return; }
  }
  
  assert(size > 0);
  tmp = __get_cont(ptr);

  if(tmp == NULL) {
    if(__warning_level == ERROR) assert(0);
    else if(__warning_level == IGNORE) return;
    else { __warning("initialize"); return; }
  }
  
  /* already fully initialized, do nothing */
  if(tmp->init_cpt == tmp->size) return;
	
  /* fully uninitialized */
  if(tmp->init_cpt == 0) {
    int nb = needed_bytes(tmp->size);
    tmp->init_ptr = malloc(nb);
    __e_acsl_memset(tmp->init_ptr, 0, nb);
  }

  for(i = 0; i < size; i++) {
    int byte_offset = (size_t)ptr - tmp->ptr + i; 
    int ind = byte_offset / 8;
    unsigned char mask_bit = 1U << (7 - (byte_offset % 8));
    if((tmp->init_ptr[ind] & mask_bit) == 0) tmp->init_cpt++;
    tmp->init_ptr[ind] |= mask_bit;
  }
  
  /* now fully initialized */
  if(tmp->init_cpt == tmp->size) {
    free(tmp->init_ptr);
    tmp->init_ptr = NULL;
  }
}

/* mark all bytes of ptr as initialized */
void __full_init (void * ptr) {
  struct _block * tmp;

  if(ptr == NULL) {
    if(__warning_level == ERROR) assert(0);
    else if(__warning_level == IGNORE) return;
    else { __warning("full_init"); return; }
  }

  tmp = __get_exact(ptr);
  
  if(tmp == NULL) {
    if(__warning_level == ERROR) assert(0);
    else if(__warning_level == IGNORE) return;
    else { __warning("full_init"); return; }
  }

  if (tmp->init_ptr != NULL) {
    free(tmp->init_ptr);
    tmp->init_ptr = NULL;
  }
  
  tmp->init_cpt = tmp->size;
}

/* mark a block as litteral string */
void __literal_string (void * ptr) {
  struct _block * tmp;

  if(ptr == NULL) {
    if(__warning_level == ERROR) assert(0);
    else if(__warning_level == IGNORE) return;
    else { __warning("literal_string"); return; }
  }

  tmp = __get_exact(ptr);
  
  if(tmp == NULL) {
    if(__warning_level == ERROR) assert(0);
    else if(__warning_level == IGNORE) return;
    else { __warning("literal_string"); return; }
  }

  tmp->is_litteral_string = true;
}

/* return whether the size bytes of ptr are initialized */
int __initialized (void * ptr, size_t size) {
  struct _block * tmp;
  unsigned i;
  assert(ptr != NULL);
  assert(size > 0);
  tmp = __get_cont(ptr);
  if(tmp == NULL)
    return false;
  
  /* fully uninitialized */
  if(tmp->init_cpt == 0) return false;
  /* fully initialized */
  if(tmp->init_cpt == tmp->size) return true;
  
  for(i = 0; i < size; i++) {
    /* if one byte is uninitialized */
    int byte_offset = (size_t)ptr - tmp->ptr + i; 
    int ind = byte_offset / 8;
    unsigned char mask_bit = 1U << (7 - (byte_offset % 8));
    if((tmp->init_ptr[ind] & mask_bit) == 0) return false;
  }
  return true;
}

/* return the length (in bytes) of the block containing ptr */
size_t __block_length(void* ptr) {
  struct _block * tmp;
  assert(ptr != NULL);
  tmp = __get_cont(ptr);
  assert(tmp != NULL);
  return tmp->size;
}

/* return whether the size bytes of ptr are readable/writable */
int __valid(void* ptr, size_t size) {
  struct _block * tmp;
  if(ptr == NULL)
    return false;
  assert(size > 0);
  tmp = __get_cont(ptr);
  return (tmp == NULL) ?
    false : ( tmp->size - ( (size_t)ptr - tmp->ptr ) >= size
	      && !tmp->is_litteral_string && !tmp->is_out_of_bound);
}

/* return whether the size bytes of ptr are readable */
int __valid_read(void* ptr, size_t size) {
  struct _block * tmp;
  if(ptr == NULL)
    return false;
  assert(size > 0);
  tmp = __get_cont(ptr);
  return (tmp == NULL) ?
    false : ( tmp->size - ( (size_t)ptr - tmp->ptr ) >= size
	      && !tmp->is_out_of_bound);
}

/* return the base address of the block containing ptr */
void* __base_addr(void* ptr) {
  struct _block * tmp;
  assert(ptr != NULL);
  tmp = __get_cont(ptr);
  assert(tmp != NULL);
  return (void*)tmp->ptr;
}

/* return the offset of ptr within its block */
int __offset(void* ptr) {
  struct _block * tmp;
  assert(ptr != NULL);
  tmp = __get_cont(ptr);
  assert(tmp != NULL);
  return ((size_t)ptr - tmp->ptr);
}

void __out_of_bound(void* ptr, _Bool flag) {
  struct _block * tmp;
  assert(ptr != NULL);
  tmp = __get_cont(ptr);
  assert(tmp != NULL);
  tmp->is_out_of_bound = flag;
}

/*******************/
/* PRINT           */
/*******************/

/* print the information about a block */
void __print_block (struct _block * ptr) {
  if (ptr != NULL) {
    printf("%p; %zu Bytes; %slitteral; [init] : %li ",
	   (char*)ptr->ptr, ptr->size,
	   ptr->is_litteral_string ? "" : "not ", ptr->init_cpt);
    if(ptr->init_ptr != NULL) {
      unsigned i;
      for(i = 0; i < ptr->size; i++) {
	int ind = i / 8;
	int one_bit = (unsigned)1 << (8 - (i % 8) - 1);
	printf("%i", (ptr->init_ptr[ind] & one_bit) != 0);
      }
    }
    printf("\n");
  }
}

/********************/
/* CLEAN            */
/********************/

/* erase information about initialization of a block */
void __clean_init (struct _block * ptr) {
  if(ptr->init_ptr != NULL) {
    free(ptr->init_ptr);
    ptr->init_ptr = NULL;
  }
  ptr->init_cpt = 0;
}

/* erase all information about a block */
void __clean_block (struct _block * ptr) {
  if(ptr == NULL) return;
  __clean_init(ptr);
  free(ptr);
}

/* erase the content of the abstract structure */
void __e_acsl_memory_clean() {
  __clean_struct();
}

/**********************/
/* DEBUG              */
/**********************/

/* print the content of the abstract structure */
void __debug() {
  __debug_struct();
}
