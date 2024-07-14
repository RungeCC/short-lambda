#include <iostream>
#include <type_traits>

import short_lambda;

using namespace short_lambda;

template < class X > void foo( X&& ) {
  if constexpr ( std::is_lvalue_reference_v< X&& > ) {
    std::cout << "lvalue ";
  } else {
    std::cout << "rvalue ";
  }
  if constexpr ( std::is_const_v< std::remove_reference_t< X > > ) {
    std::cout << "const" << std::endl;
  } else {
    std::cout << "" << std::endl;
  }
}

int main( ) {
  int const a  = 44; // ref
  int       b  = 21; // for rvalue
  int&&     c  = 3;
  auto      tp = details::forward_as_tuple( a, b, static_cast<int const&&>(c), 1 );
  foo( details::get< 0 >( tp ) );
  foo( details::get< 1 >( tp ) );
  foo( details::get< 2 >( tp ) );
  foo( details::get< 3 >( tp ) );
  foo( details::get< 0 >( std::move( tp ) ) );
  foo( details::get< 1 >( std::move( tp ) ) );
  foo( details::get< 2 >( std::move( tp ) ) );
  foo( details::get< 3 >( std::move( tp ) ) );
  std::cout << details::get< 0 >( tp ) << " " << details::get< 1 >( tp ) << " "
            << details::get< 2 >( tp ) << " " << details::get< 3 >( tp ) << std::endl;
}
