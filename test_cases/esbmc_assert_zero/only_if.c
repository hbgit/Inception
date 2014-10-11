#include <stdio.h>
#include <assert.h>

//esbmc --64 --no-library --claim [1|2|3|4] --no-slice simple_if.c
/**
 * With this claims we get the following coverage:
 *  {15,18,21,26,30}
 * 
 * 
 **/

main(){
	
	int k,l;
	int r = 2;
	
	if(l == 0){
		r = 3;
		l = 2;
		k = 5;
	}
}
