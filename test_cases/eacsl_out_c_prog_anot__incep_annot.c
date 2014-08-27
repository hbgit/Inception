/* Updated by Inception */ 
/* Generated by Frama-C */
struct __anonstruct___mpz_struct_1 {
   int _mp_alloc ;
   int _mp_size ;
   unsigned long *_mp_d ;
};
typedef struct __anonstruct___mpz_struct_1 __mpz_struct;
typedef __mpz_struct ( __attribute__((__FC_BUILTIN__)) mpz_t)[1];
typedef unsigned int size_t;
typedef unsigned int ino_t;
typedef unsigned int gid_t;
typedef unsigned int uid_t;
typedef long time_t;
typedef unsigned int blkcnt_t;
typedef unsigned int blksize_t;
typedef unsigned int dev_t;
typedef unsigned int mode_t;
typedef unsigned int nlink_t;
typedef long off_t;
struct stat {
   dev_t st_dev ;
   ino_t st_ino ;
   mode_t st_mode ;
   nlink_t st_nlink ;
   uid_t st_uid ;
   gid_t st_gid ;
   dev_t st_rdev ;
   off_t st_size ;
   time_t st_atime ;
   time_t st_mtime ;
   time_t st_ctime ;
   blksize_t st_blksize ;
   blkcnt_t st_blocks ;
   char *__fc_real_data ;
   int __fc_real_data_max_size ;
};
struct __fc_FILE {
   unsigned int __fc_stdio_id ;
   unsigned int __fc_maxsz ;
   unsigned int __fc_writepos ;
   unsigned int __fc_readpos ;
   int __fc_is_a_socket ;
   int mode ;
   struct stat *__fc_inode ;
};
typedef struct __fc_FILE FILE;
/*@ requires predicate ≢ 0;
    assigns \nothing; */
extern  __attribute__((__FC_BUILTIN__)) void e_acsl_assert(int predicate,
                                                           char *kind,
                                                           char *fct,
                                                           char *pred_txt,
                                                           int line);

/*@
model __mpz_struct { ℤ n };
*/
int __fc_random_counter __attribute__((__unused__));
unsigned long const __fc_rand_max = (unsigned long)32767;
/*@ ghost extern int __fc_heap_status; */

/*@
axiomatic
  dynamic_allocation {
  predicate is_allocable{L}(size_t n) 
    reads __fc_heap_status;
  
  }
 */
/*@ ghost extern int __e_acsl_init; */

/*@ ghost extern int __e_acsl_internal_heap; */

extern size_t __memory_size;

/*@
predicate diffSize{L1, L2}(ℤ i) =
  \at(__memory_size,L1)-\at(__memory_size,L2) ≡ i;
 */
FILE __fc_fopen[2];
FILE const *_p__fc_fopen = (FILE const *)(__fc_fopen);
int buffer[10];
int range_updated = 10;
int handle_buffer(void);

/*@ requires range ≡ 0 ∨ \valid(vet+(0 .. range-1)); */
void check_range(int range, int *vet)
{
  int i;
  int var_a;
  var_a = 2;
  i = 0;
  while (i < 10) {
    /*@ assert i < range_updated; */
assert( i < range_updated); 
    *(vet + i) = 1 * var_a;
    var_a = i * var_a + range;
    i ++;
  }
  if (range < 10) {
    range_updated = range;
    handle_buffer();
  }
  return;
}

/*@ requires range ≡ 0 ∨ \valid(vet+(0 .. range-1)); */
void __e_acsl_check_range(int range, int *vet)
{
  check_range(range,vet);
  return;
}

int handle_buffer(void)
{
  int __e_acsl_at_6;
  int __e_acsl_at_5;
  int __e_acsl_at_4;
  int __e_acsl_at_3;
  int __e_acsl_at_2;
  int __e_acsl_at;
  int __retres;
  int i;
  /*@ requires i ≡ buffer[i];
      requires (int *)buffer ≡ \null;
      requires ∀ int i; 0 ≤ i ∧ i ≤ 9 ⇒ buffer[i] ≡ 0;
  */
  {
    int __e_acsl_forall;
    int __e_acsl_i;
assert( i < 10); 
assert( 0 <= i); 
__ESBMC_assume( i == buffer[i]); 
__ESBMC_assume( buffer == (void *)0); 
    __e_acsl_forall = 1;
    __e_acsl_i = 0;
    while (1) {
      if (__e_acsl_i <= 9) ; else break;
assert( __e_acsl_i < 10); 
assert( 0 <= __e_acsl_i); 
      if (buffer[__e_acsl_i] == 0) ;
      else {
        __e_acsl_forall = 0;
        goto e_acsl_end_loop1;
      }
      __e_acsl_i ++;
    }
    e_acsl_end_loop1: ;
__ESBMC_assume( buffer[__e_acsl_i] == 0); 
__ESBMC_assume( __e_acsl_i <= 9); 
    __e_acsl_at_6 = i;
assert( (long long)i - (long long)1 < (long long)10); 
assert( 0LL <= (long long)i - (long long)1); 
    __e_acsl_at_5 = buffer[(long long)i - (long long)1];
    __e_acsl_at_4 = i;
    __e_acsl_at_3 = i;
    __e_acsl_at_2 = i;
    __e_acsl_at = i;
    i = 0;
  }
  {
    int __e_acsl_forall_2;
    int __e_acsl_k;
    int __e_acsl_forall_3;
    int __e_acsl_j;
    __e_acsl_forall_2 = 1;
    __e_acsl_k = 0;
    while (1) {
      if (__e_acsl_k <= 9) ; else break;
assert( __e_acsl_k < 10); 
assert( 0 <= __e_acsl_k); 
      if (buffer[__e_acsl_k] != __e_acsl_at) ;
      else {
        __e_acsl_forall_2 = 0;
        goto e_acsl_end_loop2;
      }
      __e_acsl_k ++;
    }
    e_acsl_end_loop2: ;
assert( buffer[__e_acsl_k] != __e_acsl_at); 
assert( __e_acsl_k <= 9); 
    __e_acsl_forall_3 = 1;
    __e_acsl_j = 0;
    while (1) {
      if (__e_acsl_j <= 9) ; else break;
assert( __e_acsl_j < 10); 
assert( 0 <= __e_acsl_j); 
      if (buffer[__e_acsl_j] == i) ;
      else {
        __e_acsl_forall_3 = 0;
        goto e_acsl_end_loop3;
      }
      __e_acsl_j ++;
    }
    e_acsl_end_loop3: ;
assert( buffer[__e_acsl_j] == i); 
assert( __e_acsl_j <= 9); 
    /*@ loop invariant ∀ int j; 0 ≤ j ∧ j ≤ 9 ⇒ buffer[j] ≡ i;
        loop invariant
          ¬(∀ int k; 0 ≤ k ∧ k ≤ 9 ⇒ buffer[k] ≢ \at(i,Pre));
    */
    while (i <= range_updated) {
      buffer[i] = i;
      {
        int __e_acsl_forall_4;
        int __e_acsl_j_2;
        int __e_acsl_forall_5;
        int __e_acsl_k_2;
        i ++;
        __e_acsl_forall_4 = 1;
        __e_acsl_j_2 = 0;
        while (1) {
          if (__e_acsl_j_2 <= 9) ; else break;
assert( __e_acsl_j_2 < 10); 
assert( 0 <= __e_acsl_j_2); 
          if (buffer[__e_acsl_j_2] == i) ;
          else {
            __e_acsl_forall_4 = 0;
            goto e_acsl_end_loop4;
          }
          __e_acsl_j_2 ++;
        }
        e_acsl_end_loop4: ;
assert( buffer[__e_acsl_j_2] == i); 
assert( __e_acsl_j_2 <= 9); 
        __e_acsl_forall_5 = 1;
        __e_acsl_k_2 = 0;
        while (1) {
          if (__e_acsl_k_2 <= 9) ; else break;
assert( __e_acsl_k_2 < 10); 
assert( 0 <= __e_acsl_k_2); 
          if (buffer[__e_acsl_k_2] != __e_acsl_at_2) ;
          else {
            __e_acsl_forall_5 = 0;
            goto e_acsl_end_loop5;
          }
          __e_acsl_k_2 ++;
        }
        e_acsl_end_loop5: ;
assert( buffer[__e_acsl_k_2] != __e_acsl_at_2); 
assert( __e_acsl_k_2 <= 9); 
      }
    }
  }
  /*@ assert i ≡ 9; */
assert( i == 9); 
  /*@ assert \at(i,Pre) ≡ buffer[\at(i,Pre)]; */
assert( __e_acsl_at_4 < 10); 
assert( 0 <= __e_acsl_at_4); 
assert( __e_acsl_at_3 == buffer[__e_acsl_at_4]); 
  /*@ assert \at(buffer[\at(i,Here)-1],Pre) ≡ buffer[\at(i,Pre)]; */
assert( __e_acsl_at_6 < 10); 
assert( 0 <= __e_acsl_at_6); 
assert( __e_acsl_at_5 == buffer[__e_acsl_at_6]); 
  /*@ assert \false; */
assert( 0); 
  __retres = 0;
  return __retres;
}

int main(void)
{
  int __retres;
  range_updated = 10;
  __e_acsl_check_range(8,buffer);
  __retres = 1;
  return __retres;
}


