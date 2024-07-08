#define SL_expr_equiv_bare( ... )                                                                  \
  { return ( __VA_ARGS__ ); } // extra parenthesis for decltype(auto)

#define SL_expr_equiv_spec( ... )                                                                  \
  noexcept( noexcept( __VA_ARGS__ ) )                                                              \
      ->decltype( auto )                                                                           \
    requires requires { __VA_ARGS__; }

#define SL_expr_equiv( ... ) SL_expr_equiv_spec( __VA_ARGS__ ) SL_expr_equiv_bare( __VA_ARGS__ )

#define SL_expr_equiv_no_ret( ... )                                                                \
  noexcept( noexcept( __VA_ARGS__ ) )                                                              \
    requires requires { __VA_ARGS__; }                                                             \
  SL_expr_equiv_bare( __VA_ARGS__ )

#define SL_expr_equiv_declval( req, ... )                                                          \
  SL_expr_equiv_spec( req ) SL_expr_equiv_bare( __VA_ARGS__ )

#define SL_noexcept_equiv_conditional( cond, b1, b2 )                                              \
  noexcept( []( ) constexpr {                                                                      \
    if constexpr ( cond )                                                                          \
      return noexcept( b1 );                                                                       \
    else                                                                                           \
      return noexcept( b2 );                                                                       \
  }( ) )
#define SL_SFINAE_equiv_conditional( cond, b1, b2 )                                                \
  requires ( []( ) constexpr {                                                                     \
    if constexpr ( cond )                                                                          \
      return requires { b1; };                                                                     \
    else                                                                                           \
      return requires { b2; };                                                                     \
  }( ) )
#define SL_body_equiv_conditional( cond, b1, b2 )                                                  \
  {                                                                                                \
    if constexpr ( cond ) {                                                                        \
      return ( b1 );                                                                               \
    } else {                                                                                       \
      return ( b2 );                                                                               \
    }                                                                                              \
  }
#define SL_expr_equiv_conditional( cond, b1, b2, b1dv, b2dv )                                      \
  SL_noexcept_equiv_conditional( cond, b1dv, b2dv )                                                \
      ->decltype( auto )                                                                           \
          SL_SFINAE_equiv_conditional( cond, b1dv, b2dv )                                          \
              SL_body_equiv_conditional( cond, b1, b2 )

#define SL_forward_like_app( ... )                                                                 \
  details::forward_like< Self >( __VA_ARGS__ )( std::forward< Ts >( args )... )

#define SL_remove_parenthesis_1( ... ) __VA_ARGS__
#define SL_remove_parenthesis_0( X )   X
#define SL_remove_parenthesis( X )     SL_remove_parenthesis_0( SL_remove_parenthesis_1 X )

#define SL_using_st( name )            constexpr inline name [[maybe_unused]]
#define SL_using_v                     [[maybe_unused]] static constexpr inline auto
#define SL_using_m                     [[maybe_unused]] constexpr inline auto
#define SL_using_f                     [[maybe_unused]] friend constexpr inline auto
#if defined( SL_cxx_msvc )
/// @note: msvc currently do not support `static operator()`
#  define SL_using_c [[maybe_unused]] constexpr inline auto
#else
#  define SL_using_c [[maybe_unused]] static constexpr inline auto
#endif