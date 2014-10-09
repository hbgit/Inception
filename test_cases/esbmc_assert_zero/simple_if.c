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
	
	if(l){
		r = 3;
		assert(0);
	}else{
		r = 5;
		assert(0);
	}
	
	if(k){
		r = 6;
		assert(0);
	}
	if(l){
		r = 7;
		assert(0);
	}
		
	
}
