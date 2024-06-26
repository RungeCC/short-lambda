#include "short-lambda.hpp"

using namespace short_lambda;

#include <iostream>

struct P {
  void operator!( ) noexcept { }
};

struct Q {
  void operator!( ) noexcept( false ) { }
};

struct R {
  void operator+(P const&)  { }
};

int main( ) {
  static_assert( noexcept( ( ! $0 )( P{ } ) ) );
  static_assert( ! noexcept( ( ! $0 )( Q{ } ) ) );
}