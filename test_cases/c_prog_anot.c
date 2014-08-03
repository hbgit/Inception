#include <stdio.h>

#define MAX 10
int buffer[MAX];
int range_updated=MAX;

/*@ requires range == 0 || \valid(vet+(0..range-1));*/
void check_range(int range, int vet[]){
  int i;
  int var_a = 2;  
  		
  for(i=0;i<MAX;i++){
	//@ assert i < range_updated;
    vet[i]=1*var_a;
    var_a = i * var_a + range;
  }

  if(range < MAX){
    range_updated=range;
    handle_buffer();     
  }
  
}

handle_buffer(){
	
  /*@ requires i == buffer[i];
    @ requires buffer == \null;
    @ requires (\forall int i; (0 <= i && i <= 9) ==> (buffer[i] == 0));                   
  */    
  
  int i;
  
  // From Daikon
  // \forall int i; (0 <= i && i <= 9) ==> (buffer[i] == i);
  // !(\forall int i; (0 <= i && i <= 9) ==> (buffer[i] != \at(i,Pre)));       
  
  //OBS: a variavel para percorrer o forall não pode ser a mesma do programa
  
  //New
  /*@ loop invariant \forall int j; (0 <= j && j <= 9) ==> (buffer[j] == i);
    loop invariant !(\forall int k; (0 <= k && k <= 9) ==> (buffer[k] != \at(i,Pre)));       
      */ 

  for(i=0; i<=range_updated;i++){
    buffer[i]=i; // BUG?
  } 
  
  //@ assert i == 9;
  //@ assert \at(i,Pre) == buffer[\at(i,Pre)];	    
  //@ assert \at(buffer[\at(i,Here)-1],Pre) == buffer[\at(i,Pre)];
  // !(\forall int i; (0 <= i && i <= 9) ==> (buffer[i] != \at(i,Pre)));
  
}

int main(){
  range_updated = MAX;
  check_range(8,buffer);  
  return 1;
}
