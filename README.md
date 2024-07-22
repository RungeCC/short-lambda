## Short Lambda

- Inspired by Boost.Lambda2.
- Keep expression equivalent-ness, i.e.:
  - Forwarding type categories, `noexcept`-ness;
  - SFINAE-friendly (through `requires` clause).

## Known issues

- There're some known ICEs related to try to capture variables inside some contexts in low versions of clang (17, for example)
- `gcc` failed to compile `fmap.cpp` due to a bug in its module implementation (successes to compile if using header file).
- Currently `msvc` can only use header file due to [we can not use "deducing this" inside msvc export module declaration](https://developercommunity.visualstudio.com/t/ICE-when-using-explicit-this-parameterD/10236618). 