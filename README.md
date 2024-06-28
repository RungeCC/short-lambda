## Short Lambda

- Inspired by Boost.Lambda2.
- Currently, does not support assignment operators
- Currently, does not support function call, subscript, and member access operators.
- Keep expression equivalent-ness, i.e.:
  - Forwarding type categories, `noexcept`-ness;
  - SFINAE-friendly (through `requires` clause).
