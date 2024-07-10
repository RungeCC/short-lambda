#include <iostream>

import short_lambda;

using namespace short_lambda;

int main( ) {
  auto ptr = static_cast< auto ( * )( std::basic_ostream< char >& )->std::basic_ostream< char >& >( std::endl );

  ( ($( std::cin ) >> $_< int, 0 > >> $_< double, 1 >)
        .then( $( std::cout ) << $_< int, 0 > << $( " and " ) << $_< double, 1 > << $( ptr ) ) )( 3 );
}
