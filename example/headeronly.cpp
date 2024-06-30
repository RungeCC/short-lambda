#include <iostream>

#include "short-lambda.hpp"

using namespace short_lambda;


struct P {
  void operator!( ) noexcept { }
};

struct Q {
  void operator!( ) noexcept( false ) { }
};

struct R {
  void operator+( P const& ) { }
};


template < auto x > struct K { };

//
int main( ) {
  auto ptr = static_cast< auto ( * )( std::basic_ostream< char >& )->std::basic_ostream< char >& >( std::endl );

  ( ($_( std::cin ) >> _$< int, 0 > >> _$< double, 1 >)
        .then( $_( std::cout ) << _$< int, 0 > << $_( " and " ) << _$< double, 1 > << $_( ptr ) ) )( 3 );
}
