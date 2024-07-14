#include <iostream>

import short_lambda;

using namespace short_lambda;

int bar(int) { return 0;}
int bar(int, int) { return 0;}

int main( ) {
  auto v  = (new_(std::type_identity<int>{}, $0).template delete_<false>().then($0))(1,2);
  std::cout << v << std::endl;
}
