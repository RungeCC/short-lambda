#include <iomanip>
#include <iostream>

import short_lambda;

using namespace short_lambda;

struct has_noexcept_not {
  bool operator!( ) noexcept { return true; }
};

struct has_not_noexcept_not {
  bool operator!( ) { return false; }
};

int main( ) {
  std::cout << std::boolalpha << ( ( not $( has_noexcept_not{ } ) ).noexcept_( )( ) ) << std::endl;
  std::cout << std::boolalpha << ( ( not $( has_not_noexcept_not{ } ) ).noexcept_( )( ) )
            << std::endl;
}
