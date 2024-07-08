#include <iostream>
#include <type_traits>


import short_lambda;

using namespace short_lambda;


int main( ) {
  auto v  = (new_(std::type_identity<int>{}, $0).template delete_<false>().then($0))(1,2);
  std::cout << v << std::endl;
}
