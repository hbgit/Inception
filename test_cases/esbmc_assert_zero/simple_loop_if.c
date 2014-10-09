#include <stdio.h>
#include <assert.h>

//esbmc --64 --no-library --claim [1|2|3] --no-slice simple_if.c
/**
 * With this claims we get the following coverage:
 *  {15,24,26,29,35,37,38}
 * 
 * 
 **/

main(){
	
	int k,l;
	int r = 2;
	
	//How Could I reduze the number of asserts zero added?
	// ANS: Take as base the process, we should avoid to add
	//      asserts(0) in the last part of control component (if,while,...)
	//		when the line before the actual line is not a assignment or Decl.
	
	if(nondet_int()){
		while(r < 50){
			r = r + nondet_int();
			if(r > 53){
				r = 53;
				assert(0);
			}else{
				r = 0;
				assert(0);
			}
			//assert(0); //why?
		}
		
		l = 13;
		
		for(k=0; k <= r; k++){
			int t = 2;
			assert(0);
		}
		
		//assert(0); //why?
	}
	
	//only we add an assertion if we find some statement
	
}
