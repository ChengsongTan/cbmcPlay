#include <stdio.h>
#include <assert.h>

void f();
#define UNWRAP(X)  do {} while(0)
void f(){

}

int main(){
	UNWRAP(0);

	f();
	char * y = malloc(10);
	char * x = malloc(10);
	memset(x,1,1);
	//__CPROVER_assert(0,"smoke");
	return 1;
}
