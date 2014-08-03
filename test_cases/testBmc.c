#include <stdio.h>
#include <assert.h>

#define check(cond)   if(!(cond)){ printf("BUG \n"); assert(0); }
            
        

main()
{
    int vet[3];
    int i = 5;
    //vet[i] << (i < 3)
    check(i<10);    
}
