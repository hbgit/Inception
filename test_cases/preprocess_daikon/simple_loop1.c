/**
 * gcc -gdwarf-2 simple_loop1.c -o simple_loop1
 * 
 * kvasir-dtrace ./simple_loop1
 * 
 * java daikon.Daikon --config_option daikon.derive.Derivation.disable_derived_variables=true daikon-output/simple_loop1.dtrace
 * 
 * 
 * STATUS: BUG in some translation rules
 * 
 * */

#include <stdio.h>

int arr[5] = {2,3,1,2,2};

int foo(int N){
	int i=0;
	while(i < N){
		arr[i] = arr[i] * i;
		i++;
	}
	
	return arr[i];
}	

main(){
	
	int a = foo(5);
	
}
