#include "short-lambda.hpp"

#include <type_traits>

using namespace short_lambda;

#include <iostream>

struct P {
  void operator!( ) noexcept { }
};

struct Q {
  void operator!( ) noexcept( false ) { }
};

struct R {
  void operator+( P const& ) { }
};

template < class T >
  requires std::is_default_constructible_v< T >
struct storage_t {
  T                                          value;

  template < class U, class Self > constexpr operator U&( this Self&& self ) {
    return details::forward_like< Self >( self.value );
  }

  template < class... Ts, class Self > constexpr decltype( auto ) operator( )( this Self&& self, Ts&&... args ) {
    return details::forward_like< Self >( self.value );
  }
};


template < class T, std::size_t id = 0 > inline static storage_t< T > storage{ };

template < class U, std::size_t id = 0 > constexpr inline static auto _$ = coprojector_t< U >{ }( storage< U, id > );

//
int main( ) {
  auto ptr = static_cast< auto ( * )( std::basic_ostream< char >& )->std::basic_ostream< char >& >( std::endl );



  ( ($_( std::cin ) >> _$< int , 0> >> _$<int, 1>)).then( ( $_( std::cout ) << (_$< int, 0 > + _$<int, 1> * $0) << $_( ptr ) ) )(
    23
  );
}
