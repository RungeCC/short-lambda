#include "short-lambda.hpp"

using namespace short_lambda;

#include <iostream>

int main( ) {
  ($_$(std::cout) << $_(std::string{"The result of: a * b + c is: "}) << ($0 * $1 + $2))(19, 20, 21);

}