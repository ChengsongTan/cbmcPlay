#include <stdlib.h>
int main() {
  size_t initial_size;
  size_t requested_size;

  size_t size = initial_size;
  while (size < requested_size) {
    size *= 2;
  }
}

