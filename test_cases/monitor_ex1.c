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

/*@ assigns \result;
    assigns \result \from *((char *)ptr+(0 .. size-1)); */
extern  __attribute__((__FC_BUILTIN__)) void *__store_block(void *ptr,
                                                            size_t size);

/*@ assigns \nothing; */
extern  __attribute__((__FC_BUILTIN__)) void __delete_block(void *ptr);

/*@ assigns \nothing; */
extern  __attribute__((__FC_BUILTIN__)) void __initialize(void *ptr,
                                                          size_t size);

/*@ ghost extern int __e_acsl_internal_heap; */

/*@ assigns __e_acsl_internal_heap;
    assigns __e_acsl_internal_heap \from __e_acsl_internal_heap;
 */
extern  __attribute__((__FC_BUILTIN__)) void __e_acsl_memory_clean(void);

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
    e_acsl_assert(i < range_updated,(char *)"Assertion",
                  (char *)"check_range",(char *)"i < range_updated",13);
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
  __store_block((void *)(& vet),4U);
  check_range(range,vet);
  __delete_block((void *)(& vet));
  return;
}

int handle_buffer(void)
{
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
    e_acsl_assert(i < 10,(char *)"RTE",(char *)"handle_buffer",
                  (char *)"index_bound: i < 10",27);
    e_acsl_assert(0 <= i,(char *)"RTE",(char *)"handle_buffer",
                  (char *)"index_bound: 0 <= i",27);
    e_acsl_assert(i == buffer[i],(char *)"Precondition",
                  (char *)"handle_buffer",(char *)"i == buffer[i]",27);
    e_acsl_assert(buffer == (void *)0,(char *)"Precondition",
                  (char *)"handle_buffer",(char *)"(int *)buffer == \\null",
                  28);
    __e_acsl_forall = 1;
    __e_acsl_i = 0;
    while (1) {
      if (__e_acsl_i <= 9) ; else break;
      e_acsl_assert(__e_acsl_i < 10,(char *)"RTE",(char *)"handle_buffer",
                    (char *)"index_bound: __e_acsl_i < 10",29);
      e_acsl_assert(0 <= __e_acsl_i,(char *)"RTE",(char *)"handle_buffer",
                    (char *)"index_bound: 0 <= __e_acsl_i",29);
      if (buffer[__e_acsl_i] == 0) ;
      else {
        __e_acsl_forall = 0;
        goto e_acsl_end_loop1;
      }
      __e_acsl_i ++;
    }
    e_acsl_end_loop1: ;
    e_acsl_assert(__e_acsl_forall,(char *)"Precondition",
                  (char *)"handle_buffer",
                  (char *)"\\forall int i; 0 <= i && i <= 9 ==> buffer[i] == 0",
                  29);
    __e_acsl_at_5 = __e_acsl_i_4;
    __e_acsl_at_4 = i;
    e_acsl_assert((long long)i - (long long)1 < (long long)10,(char *)"RTE",
                  (char *)"handle_buffer",
                  (char *)"index_bound: (long long)((long long)i-(long long)1) < 10",
                  41);
    e_acsl_assert(0LL <= (long long)i - (long long)1,(char *)"RTE",
                  (char *)"handle_buffer",
                  (char *)"index_bound: 0 <= (long long)((long long)i-(long long)1)",
                  41);
    __store_block((void *)(& __e_acsl_at_3),4U);
    __e_acsl_at_3 = buffer[(long long)i - (long long)1];
    __e_acsl_at_2 = i;
    __e_acsl_at = i;
    i = 0;
  }
  {
    int __e_acsl_forall_2;
    int __e_acsl_i_2;
    __e_acsl_forall_2 = 1;
    __e_acsl_i_2 = 0;
    while (1) {
      if (__e_acsl_i_2 <= 9) ; else break;
      e_acsl_assert(__e_acsl_i_2 < 10,(char *)"RTE",(char *)"handle_buffer",
                    (char *)"index_bound: __e_acsl_i_2 < 10",34);
      e_acsl_assert(0 <= __e_acsl_i_2,(char *)"RTE",(char *)"handle_buffer",
                    (char *)"index_bound: 0 <= __e_acsl_i_2",34);
      if (buffer[__e_acsl_i_2] == __e_acsl_i_2) ;
      else {
        __e_acsl_forall_2 = 0;
        goto e_acsl_end_loop2;
      }
      __e_acsl_i_2 ++;
    }
    e_acsl_end_loop2: ;
    e_acsl_assert(__e_acsl_forall_2,(char *)"Invariant",
                  (char *)"handle_buffer",
                  (char *)"\\forall int i; 0 <= i && i <= 9 ==> buffer[i] == i",
                  34);
    /*@ loop invariant ∀ int i; 0 ≤ i ∧ i ≤ 9 ⇒ buffer[i] ≡ i; */
    while (i <= range_updated) {
      __initialize((void *)(& buffer[i]),sizeof(int));
      buffer[i] = i;
      {
        int __e_acsl_forall_3;
        int __e_acsl_i_3;
        i ++;
        __e_acsl_forall_3 = 1;
        __e_acsl_i_3 = 0;
        while (1) {
          if (__e_acsl_i_3 <= 9) ; else break;
          e_acsl_assert(__e_acsl_i_3 < 10,(char *)"RTE",
                        (char *)"handle_buffer",
                        (char *)"index_bound: __e_acsl_i_3 < 10",34);
          e_acsl_assert(0 <= __e_acsl_i_3,(char *)"RTE",
                        (char *)"handle_buffer",
                        (char *)"index_bound: 0 <= __e_acsl_i_3",34);
          if (buffer[__e_acsl_i_3] == __e_acsl_i_3) ;
          else {
            __e_acsl_forall_3 = 0;
            goto e_acsl_end_loop3;
          }
          __e_acsl_i_3 ++;
        }
        e_acsl_end_loop3: ;
        e_acsl_assert(__e_acsl_forall_3,(char *)"Invariant",
                      (char *)"handle_buffer",
                      (char *)"\\forall int i; 0 <= i && i <= 9 ==> buffer[i] == i",
                      34);
      }
    }
  }
  /*@ assert i ≡ 9; */
  e_acsl_assert(i == 9,(char *)"Assertion",(char *)"handle_buffer",
                (char *)"i == 9",39);
  /*@ assert \at(i,Pre) ≡ buffer[\at(i,Pre)]; */
  e_acsl_assert(__e_acsl_at_2 < 10,(char *)"RTE",(char *)"handle_buffer",
                (char *)"index_bound: __e_acsl_at_2 < 10",0);
  e_acsl_assert(0 <= __e_acsl_at_2,(char *)"RTE",(char *)"handle_buffer",
                (char *)"index_bound: 0 <= __e_acsl_at_2",0);
  e_acsl_assert(__e_acsl_at == buffer[__e_acsl_at_2],(char *)"Assertion",
                (char *)"handle_buffer",
                (char *)"\\at(i,Pre) == buffer[\\at(i,Pre)]",40);
  /*@ assert \at(buffer[\at(i,Here)-1],Pre) ≡ buffer[\at(i,Pre)]; */
  e_acsl_assert(__e_acsl_at_4 < 10,(char *)"RTE",(char *)"handle_buffer",
                (char *)"index_bound: __e_acsl_at_4 < 10",0);
  e_acsl_assert(0 <= __e_acsl_at_4,(char *)"RTE",(char *)"handle_buffer",
                (char *)"index_bound: 0 <= __e_acsl_at_4",0);
  e_acsl_assert(__e_acsl_at_3 == buffer[__e_acsl_at_4],(char *)"Assertion",
                (char *)"handle_buffer",
                (char *)"\\at(buffer[\\at(i,Here)-1],Pre) == buffer[\\at(i,Pre)]",
                41);
  /*@ assert ¬(∀ int i; 0 ≤ i ∧ i ≤ 9 ⇒ buffer[i] ≢ \at(i,Pre));
  */
  {
    int __e_acsl_forall_4;
    int __e_acsl_i_4;
    __e_acsl_forall_4 = 1;
    __e_acsl_i_4 = 0;
    while (1) {
      if (__e_acsl_i_4 <= 9) ; else break;
      e_acsl_assert(__e_acsl_i_4 < 10,(char *)"RTE",(char *)"handle_buffer",
                    (char *)"index_bound: __e_acsl_i_4 < 10",42);
      e_acsl_assert(0 <= __e_acsl_i_4,(char *)"RTE",(char *)"handle_buffer",
                    (char *)"index_bound: 0 <= __e_acsl_i_4",42);
      if (buffer[__e_acsl_i_4] != __e_acsl_at_5) ;
      else {
        __e_acsl_forall_4 = 0;
        goto e_acsl_end_loop4;
      }
      __e_acsl_i_4 ++;
    }
    e_acsl_end_loop4: ;
    e_acsl_assert(! __e_acsl_forall_4,(char *)"Assertion",
                  (char *)"handle_buffer",
                  (char *)"!(\\forall int i; 0 <= i && i <= 9 ==> buffer[i] != \\at(i,Pre))",
                  42);
  }
  /*@ assert \false; */
  e_acsl_assert(0,(char *)"Assertion",(char *)"handle_buffer",
                (char *)"\\false",44);
  __retres = 0;
  return __retres;
}

void __e_acsl_memory_init(void)
{
  __store_block((void *)(buffer),40U);
  return;
}

int main(void)
{
  int __retres;
  __e_acsl_memory_init();
  range_updated = 10;
  __e_acsl_check_range(8,buffer);
  __retres = 1;
  __delete_block((void *)(buffer));
  __e_acsl_memory_clean();
  return __retres;
}

