#if defined( _MSC_VER )
#  define SL_cxx_msvc
#elif defined( __clang__ )
#  define SL_cxx_clang
#elif defined( __GNUC__ )
#  define SL_cxx_gcc
#elif
static_assert( false, "unsupported compiler" );
#endif

#if defined(__RESHARPER__)
#define SL_anal_resharper
#elif defined(__INTELLISENSE__)
#define SL_anal_intellisense
#elif defined(__clangd__)
#define SL_anal_clangd
#endif
