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
  constexpr static auto my_not
      = fmap< lambda >( []( auto any ) noexcept( noexcept( not any ) )
                          requires requires { not any; }
                        { return not any; } );
  std::cout << std::boolalpha << ( ( my_not( $0 ) ).noexcept_( )( has_noexcept_not{ } ) )
            << std::endl;
  std::cout << std::boolalpha << ( ( my_not( $0 ) ).noexcept_( )( has_not_noexcept_not{ } ) )
            << std::endl;
}
