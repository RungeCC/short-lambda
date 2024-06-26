#include "short-lambda.hpp"

using namespace short_lambda;

#include <iostream>

struct P {
  int a{};
  int operator!() {
    return a++;
  }
};

int main( ) {
  ($_$(std::cout) << $_(std::string{"The result of: a * b + c is: "}) << ($0 * $1 + $2))(19, 20, 21);

  P p;
  std::cout << (!$0$)(p);
  std::cout << p.a;
}