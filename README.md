## Short Lambda

- Inspired by Boost.Lambda2.
- Keep [expression equivalent](https://en.cppreference.com/w/cpp/language/expressions#Expression-equivalence), i.e.:
  - Forwarding value categories (lvalue, rvalue);
  - Forwarding `noexcept`-ness;
  - Forwarding `constexpr`-ness;
  - SFINAE-friendly (through `requires` clause);
  - have the same effect.

## Supported Coompiler

Plans to support the latest versions of all major three compilers since we need the latest c++ standard (c++26) features to be supported.

The header-only case could work with:

- msvc cl from Visual Studio 17.11 (with msvc stl)
- clang 18.1 (with libc++)
- gcc 14.1 (with libstdc++)

The module-only case only works well with clang (`>=18.1`);