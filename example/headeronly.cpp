#include "short-lambda.hpp"

#include <iostream>

using namespace short_lambda;

struct V {
  int x, y;
};

int main( ) {
  auto ptr = static_cast< auto ( * )( std::basic_ostream< char >& )->std::basic_ostream< char >& >(
      std::endl );

  ( ($( std::cin ) >> $_< int, 0 > >> $_< double, 1 >)
        .then( $( std::cout ) << $_< int, 0 > << $( " and " ) << $_< double, 1 > << $( ptr ) ) )(
      3 );
  struct has_noexcept_not {
    bool operator!( ) noexcept { return true; }
  };

  struct has_not_noexcept_not {
    bool operator!( ) { return false; }
  };

  constexpr static auto my_not = fmap< lambda >( []( auto any ) noexcept( noexcept( not any ) )
                                                   requires requires { not any; }
                                                 { return not any; } );
  std::cout << std::boolalpha << ( ( my_not( $0 ) ).noexcept_( )( has_noexcept_not{ } ) )
            << std::endl;
  std::cout << std::boolalpha << ( ( my_not( $0 ) ).noexcept_( )( has_not_noexcept_not{ } ) )
            << std::endl;

  auto v = ( new_( std::type_identity< V >{ }, $0, $1 )
                 .delete_( std::integral_constant< bool, false >{ } )
                 .then( $0 ) )( 1, 2 );
  std::cout << v << std::endl;
}
