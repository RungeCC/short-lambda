## Short Lambda

- Inspired by Boost.Lambda2.
- Keep expression equivalent-ness, i.e.:
  - Forwarding type categories, `noexcept`-ness;
  - SFINAE-friendly (through `requires` clause).

## Known issues

- Lower versions of clang (`<18`) may trigger some ICEs due to some known issue in lambda capture scope.
- Currently does not support msvc due to captured lambda inside a `requires` clause triggers msvc ICE.
- Currently sometimes we use `declval<decltype((id))>` but not just `id` due to a bug in clang's capture code.