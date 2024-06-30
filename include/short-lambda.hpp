#pragma once

#include <cstddef>
#include <memory>
#include <tuple>
#include <type_traits>
#include <typeindex>
#include <utility>

#define SL_expr_equiv_bare( ... )                                                                                      \
  { return ( __VA_ARGS__ ); } // extra parenthesis for decltype(auto)

#define SL_expr_equiv( ... )                                                                                           \
  noexcept( noexcept( __VA_ARGS__ ) )                                                                                  \
      ->decltype( auto )                                                                                               \
    requires requires { __VA_ARGS__; }                                                                                 \
  SL_expr_equiv_bare( __VA_ARGS__ )

#define SL_expr_equiv_no_ret( ... )                                                                                    \
  noexcept( noexcept( __VA_ARGS__ ) )                                                                                  \
    requires requires { __VA_ARGS__; }                                                                                 \
  SL_expr_equiv_bare( __VA_ARGS__ )

#define SL_expr_equiv_declval( req, ... )                                                                              \
  noexcept( noexcept( req ) )                                                                                          \
      ->decltype( auto )                                                                                               \
    requires requires { req; }                                                                                         \
  SL_expr_equiv_bare( __VA_ARGS__ )

#define SL_forward_like_app( ... )     details::forward_like< Self >( __VA_ARGS__ )( std::forward< Ts >( args )... )
#define SL_remove_parenthesis_1( ... ) __VA_ARGS__
#define SL_remove_parenthesis_0( X )   X
#define SL_remove_parenthesis( X )     SL_remove_parenthesis_0( SL_remove_parenthesis_1 X )

#define SL_using_st( name )            static constexpr inline name [[maybe_unused]]
#define SL_using_v                     [[maybe_unused]] static constexpr inline auto
#define SL_using_m                     [[maybe_unused]] constexpr inline auto
#define SL_using_f                     [[maybe_unused]] friend constexpr inline auto


namespace short_lambda::details {
  template < class T, class U >
  concept similar_to = std::same_as< U, std::remove_cvref_t< T > >;

  template < class T, template < class... > class U, class... Us >
  concept satisfy = U< std::remove_cvref_t< T >, Us... >::value;

  template < template < class... > class U, class... Ts >
  concept any_satisfy = ( U< std::remove_cvref_t< Ts > >::value || ... );


  template < class T, class U > [[nodiscard]] constexpr auto&& forward_like( U&& x ) noexcept {
    constexpr bool is_adding_const = std::is_const_v< std::remove_reference_t< T > >;
    if constexpr ( std::is_lvalue_reference_v< T&& > ) {
      if constexpr ( is_adding_const ) {
        return std::as_const( x );
      } else {
        return static_cast< U& >( x );
      }
    } else if constexpr ( is_adding_const ) {
      return std::move( std::as_const( x ) );
    } else {
      return std::move( x );
    }
  }
} // namespace short_lambda::details


namespace short_lambda {
  template < class CallableT > struct lambda;

  template < class T > struct is_short_lambda: std::false_type { };

  template < class ClosureT > struct is_short_lambda< lambda< ClosureT > >: std::true_type { };

  enum class operators : unsigned int {
    plus = 0,
    minus,
    multiply,
    divide,
    modulus,
    negate,
    positate = 6,
    bit_and  = 7,
    bit_or,
    bit_xor,
    left_shift,
    right_shift = 10, // ^ arithmetic
    logical_and = 11,
    logical_or,
    logical_not = 13, // ^ logical
    equal_to    = 14,
    not_equal_to,
    greater,
    less,
    greater_equal,
    less_equal,
    compare_three_way = 20, // ^ comparison
    post_increment    = 21,
    pre_increment,
    post_decrement,
    pre_decrement = 24, // ^ in/de-crement
    assign_to     = 25,
    add_to,
    subtract_from,
    times_by,
    divide_by,
    modulus_with,
    bit_or_with,
    bit_and_with,
    bit_xor_with,
    left_shift_with,
    right_shift_with = 35, // ^ assignment
    function_call    = 36,
    comma,
    conditional = 38, // ^ misc
    subscript   = 39,
    address_of  = 40,
    indirection,
    object_member_access, // TBD
    pointer_member_access,
    object_member_access_of_pointer,
    pointer_member_access_of_pointer = 45, // ^ member access
    static_cast_                     = 46,
    dynamic_cast_,
    const_cast_,
    reinterpret_cast_,
    cstyle_cast, // cstyle cast, not keyword.
    sizeof_,
    alignof_,
    decltype_,
    typeid_,
    throw_,
    noexcept_,
    new_,           // TBD
    delete_,        // TBD
    co_await_ = 59, // ^ special, v extra, provide by me
    then      = 60, // expression-equivalent to `(void)lhs, rhs`
  };

  template < operators op > struct operators_t {
    SL_using_v value = op;
  };

  template < class T > struct is_operators_t: std::false_type { };

  template < operators op > struct is_operators_t< operators_t< op > >: std::true_type { };

  template < class T > struct every_operator_with_lambda_enabled: std::false_type { };

  template < details::satisfy< is_short_lambda > lambdaT >
  struct every_operator_with_lambda_enabled< lambdaT >: std::true_type { };

  template < class T, details::satisfy< is_operators_t > OpT > struct operator_with_lambda_enabled: std::false_type { };

  template < details::satisfy< every_operator_with_lambda_enabled > T, details::satisfy< is_operators_t > OpT >
  struct operator_with_lambda_enabled< T, OpT >: std::true_type { };

  namespace function_object {

#define SL_define_binary_op( name, op )                                                                                \
  struct name##_t {                                                                                                    \
    template < class LHS, class RHS >                                                                                  \
    SL_using_v operator( )( LHS&& lhs, RHS&& rhs )                                                                     \
        SL_expr_equiv( std::forward< LHS >( lhs ) SL_remove_parenthesis( op ) std::forward< RHS >( rhs ) )             \
  } SL_using_st( name ){ };

    SL_define_binary_op( plus, ( +) )
    SL_define_binary_op( minus, ( -) )
    SL_define_binary_op( multiply, (*) )
    SL_define_binary_op( divide, ( / ) )
    SL_define_binary_op( modulus, ( % ) )

    SL_define_binary_op( bit_and, (&) )
    SL_define_binary_op( bit_or, ( | ) )
    SL_define_binary_op( bit_xor, ( ^) )
    SL_define_binary_op( left_shift, ( << ) )
    SL_define_binary_op( right_shift, ( >> ) )

    SL_define_binary_op( logical_and, (&&) )
    SL_define_binary_op( logical_or, ( || ) )

    SL_define_binary_op( equal_to, ( == ) )
    SL_define_binary_op( not_equal_to, ( != ) )
    SL_define_binary_op( greater, ( > ) )
    SL_define_binary_op( less, ( < ) )
    SL_define_binary_op( greater_equal, ( >= ) )
    SL_define_binary_op( less_equal, ( <= ) )
    SL_define_binary_op( compare_three_way, ( <=> ) )

    SL_define_binary_op( comma, (, ) )

    SL_define_binary_op( pointer_member_access_of_pointer, (->*) )

    SL_define_binary_op( assign_to, ( = ) )
    SL_define_binary_op( add_to, ( += ) )
    SL_define_binary_op( subtract_from, ( -= ) )
    SL_define_binary_op( times_by, ( *= ) )
    SL_define_binary_op( divide_by, ( /= ) )
    SL_define_binary_op( modulus_with, ( %= ) )
    SL_define_binary_op( bit_or_with, ( |= ) )
    SL_define_binary_op( bit_and_with, ( &= ) )
    SL_define_binary_op( bit_xor_with, ( ^= ) )
    SL_define_binary_op( left_shift_with, ( <<= ) )
    SL_define_binary_op( right_shift_with, ( >>= ) )
#undef SL_define_binary_op // undefine


#define SL_define_unary_op( name, op )                                                                                 \
  struct name##_t {                                                                                                    \
    template < class Oprand >                                                                                          \
    SL_using_v operator( )( Oprand&& arg ) SL_expr_equiv( SL_remove_parenthesis( op ) std::forward< Oprand >( arg ) )  \
  } SL_using_st( name ){ };

    SL_define_unary_op( negate, ( -) )
    SL_define_unary_op( positate, ( +) )
    SL_define_unary_op( bit_not, ( ~) )
    SL_define_unary_op( logical_not, ( ! ) )
    SL_define_unary_op( address_of, (&) )
    SL_define_unary_op( indirection, (*) )
    SL_define_unary_op( pre_increment, ( ++) )
    SL_define_unary_op( pre_decrement, ( --) )

#undef SL_define_unary_op

    struct post_increment_t {
      template < class Oprand > SL_using_v operator( )( Oprand&& arg ) SL_expr_equiv( std::forward< Oprand >( arg )-- )
    } SL_using_st( post_increment ){ };

    struct post_decrement_t {
      template < class Oprand > SL_using_v operator( )( Oprand&& arg ) SL_expr_equiv( std::forward< Oprand >( arg )-- )
    } SL_using_st( post_decrement ){ };

    struct object_member_access_of_pointer_t {
      template < class Oprand >
      SL_using_v operator( )( Oprand&& arg ) SL_expr_equiv( std::forward< Oprand >( arg ).operator->( ) )
    } SL_using_st( object_member_access_of_pointer ){ };


    // some unoverloadable operator

    struct pointer_member_access_t { // a.*b
      template < class LHS, class RHS >
      SL_using_v operator( )( LHS&& lhs, RHS&& rhs )
          SL_expr_equiv( std::forward< LHS >( lhs ).*( std::forward< RHS >( rhs ) ) )
    } SL_using_st( pointer_member_access ){ };

    // It seems that it's impossible to implement object_member_access (a.k.a. `dot') operator.

    struct function_call_t {
      template < class F, class... Args >
      SL_using_v operator( )( F&& f, Args&&... args )
          SL_expr_equiv( std::forward< F >( f )( std::forward< Args >( args )... ) )
    } SL_using_st( function_call ){ };

    struct subscript_t {
      template < class Array, class... Idx >
      SL_using_v operator( )( Array&& arr, Idx&&... idx )
          SL_expr_equiv( std::forward< Array >( arr )[ std::forward< Idx >( idx )... ] )
    } SL_using_st( subscript ){ };

    struct conditional_t {
      template < class Cond, class TrueB, class FalseB >
      SL_using_v operator( )( Cond&& cond, TrueB&& trueb, FalseB&& falseb ) SL_expr_equiv(
          std::forward< Cond >( cond ) ? std::forward< TrueB >( trueb ) : std::forward< FalseB >( falseb ) )
    } SL_using_st( conditional ){ };

    struct static_cast_t {
      template < class Target, class Op >
      SL_using_v operator( )( Op&& arg, std::type_identity< Target > target = { } )
          SL_expr_equiv( static_cast< Target >( std::forward< Op >( arg ) ) )
    } SL_using_st( static_cast_ ){ };

    struct const_cast_t {
      template < class Target, class Op >
      SL_using_v operator( )( Op&& arg, std::type_identity< Target > target = { } )
          SL_expr_equiv( const_cast< Target >( std::forward< Op >( arg ) ) )
    } SL_using_st( const_cast_ ){ };

    struct dynamic_cast_t {
      template < class Target, class Op >
      SL_using_v operator( )( Op&& arg, std::type_identity< Target > target = { } )
          SL_expr_equiv( dynamic_cast< Target >( std::forward< Op >( arg ) ) )
    } SL_using_st( dynamic_cast_ ){ };

    struct reinterpret_cast_t {
      template < class Target, class Op >
      SL_using_v operator( )( Op&& arg, std::type_identity< Target > target = { } )
          SL_expr_equiv( reinterpret_cast< Target >( std::forward< Op >( arg ) ) )
    } SL_using_st( reinterpret_cast_ ){ };

    struct cstyle_cast_t {
      template < class Target, class Op >
      SL_using_v operator( )( Op&& arg, std::type_identity< Target > target = { } )
          SL_expr_equiv( (Target) ( std::forward< Op >( arg ) ) )
    } SL_using_st( cstyle_cast ){ };

    struct throw_t {
      template < class Op >
      /*constexpr*/ [[noreturn]] static auto operator( )( Op&& arg ) noexcept( false ) -> void
        requires requires { auto{ std::forward< Op >( arg ) }; }
      {
        throw std::forward< Op >( arg );
      }
    } SL_using_st( throw_ ){ };

    struct noexcept_t {
      /// @note: this operator can not work as expected, so we delete it
      template < class Op > SL_using_v operator( )( Op&& arg ) noexcept -> bool = delete;
    } SL_using_st( noexcept_ ){ };

    struct decltype_t {
      template < class Op, bool id = false >
      SL_using_v operator( )( Op&& arg, std::integral_constant< bool, id > = { } ) noexcept
        requires ( ( id && requires { std::type_identity< decltype( arg ) >{ }; } )
                   || ( requires { std::type_identity< decltype( ( arg ) ) >{ }; } ) )
      {
        if constexpr ( id ) {
          return std::type_identity< decltype( arg ) >{ };
        } else {
          return std::type_identity< decltype( ( arg ) ) >{ };
        }
      }
    } SL_using_st( decltype_ ){ };

    struct typeid_t {
      template < class Op >
      SL_using_v operator( )( Op&& arg ) noexcept
        requires requires { std::type_index{ typeid( arg ) }; }
      {
        return std::type_index{ typeid( arg ) };
      }
    } SL_using_st( typeid_ ){ };

    struct sizeof_t {
      template < class Op >
      SL_using_v operator( )( Op&& arg ) noexcept
        requires requires { sizeof( arg ); }
      {
        return sizeof( arg );
      }
    } SL_using_st( sizeof_ ){ };

    struct alignof_t {
      template < class Op >
      SL_using_v operator( )( Op&& arg ) noexcept
        requires requires { alignof( std::remove_cvref_t< Op > ); }
      {
        return alignof( std::remove_cvref_t< Op > );
      }
    } SL_using_st( alignof_ ){ };

    struct new_t {
      template < class T0, class... Ts >
      SL_using_v operator( )( std::type_identity< T0 > arg0, Ts&&... args )
          SL_expr_equiv( new T0{ std::forward< Ts >( args )... } )
    } SL_using_st( new_ ){ };

    struct delete_t {
      template < bool Array = false, class Op >
      SL_using_v operator( )( Op&& arg, std::integral_constant< bool, Array > = { } )
          noexcept( ( Array && noexcept( delete[] arg ) ) || ( noexcept( delete arg ) ) )
              ->decltype( auto )
        requires ( ( Array && requires { delete[] arg; } ) || ( requires { delete arg; } ) )
      {
        if constexpr ( Array ) {
          delete[] arg;
        } else {
          delete arg;
        }
      }
    } SL_using_st( delete_ ){ };

    struct co_await_t {
      template < class Op >
      SL_using_v operator( )( Op&& arg )
          noexcept( ( requires { std::forward< Op >( arg ).operator co_await( ); }
                      && noexcept( std::forward< Op >( arg ).operator co_await( ) ) )
                    || ( requires { operator co_await( std::forward< Op >( arg ) ); }
                         && noexcept( operator co_await( std::forward< Op >( arg ) ) ) ) )
              ->decltype( auto )
        requires (
            requires { std::forward< Op >( arg ).operator co_await( ); }
            || requires { operator co_await( std::forward< Op >( arg ) ); } )
      {
        if constexpr ( requires { std::forward< Op >( arg ).operator co_await( ); } ) {
          return std::forward< Op >( arg ).operator co_await( );
        } else if constexpr ( requires { operator co_await( std::forward< Op >( arg ) ); } ) {
          return operator co_await( std::forward< Op >( arg ) );
        } else {
          static_assert( false );
        }
      }
    } SL_using_st( co_await_ ){ };

    struct then_t {
      template < class LHS, class RHS >
      SL_using_v operator( )( LHS&& lhs, RHS&& rhs )
          noexcept( noexcept( lhs ) && noexcept( std::forward< RHS >( rhs ) ) )
              ->decltype( auto )
        requires requires {
                   lhs;
                   std::forward< RHS >( rhs );
                 }
      {
        lhs;
        return std::forward< RHS >( rhs );
      }
    } SL_using_st( then ){ };


  } // namespace function_object

  inline namespace lambda_operators {
#define SL_lambda_binary_operator( name, op )                                                                          \
  template < details::satisfy< operator_with_lambda_enabled, operators_t< operators::name > > LHS,                     \
             details::satisfy< operator_with_lambda_enabled, operators_t< operators::name > > RHS >                    \
    requires details::any_satisfy< is_short_lambda, LHS, RHS >                                                         \
  SL_using_m operator SL_remove_parenthesis( op )( LHS&& lhs, RHS&& rhs ) SL_expr_equiv( lambda {                      \
    [lhs{ std::forward< LHS >( lhs ) },                                                                                \
     rhs{ std::forward< RHS >( rhs ) }]< class Self, class... Ts >( this Self&& self, Ts&&... args )                   \
        SL_expr_equiv_declval(                                                                                         \
            /*req*/ ( ::short_lambda::function_object::name( SL_forward_like_app( std::declval< LHS >( ) ),            \
                                                             SL_forward_like_app( std::declval< RHS >( ) ) ) ),        \
            ::short_lambda::function_object::name( SL_forward_like_app( lhs ), SL_forward_like_app( rhs ) ) )          \
  } )

    SL_lambda_binary_operator( plus, ( +) )
    SL_lambda_binary_operator( minus, ( -) )
    SL_lambda_binary_operator( multiply, (*) )
    SL_lambda_binary_operator( divide, ( / ) )
    SL_lambda_binary_operator( modulus, ( % ) )
    SL_lambda_binary_operator( bit_and, (&) )
    SL_lambda_binary_operator( bit_or, ( | ) )
    SL_lambda_binary_operator( bit_xor, ( ^) )
    SL_lambda_binary_operator( left_shift, ( << ) )
    SL_lambda_binary_operator( right_shift, ( >> ) )
    SL_lambda_binary_operator( logical_and, (&&) )
    SL_lambda_binary_operator( logical_or, ( || ) )
    SL_lambda_binary_operator( equal_to, ( == ) )
    SL_lambda_binary_operator( not_equal_to, ( != ) )
    SL_lambda_binary_operator( greater, ( > ) )
    SL_lambda_binary_operator( less, ( < ) )
    SL_lambda_binary_operator( greater_equal, ( >= ) )
    SL_lambda_binary_operator( less_equal, ( <= ) )
    SL_lambda_binary_operator( compare_three_way, ( <=> ) )
    SL_lambda_binary_operator( comma, (, ) )
    SL_lambda_binary_operator( pointer_member_access_of_pointer, (->*) )

#undef SL_lambda_binary_operator


#define SL_lambda_unary_operator( name, op )                                                                           \
  template < details::satisfy< is_short_lambda > Oprand >                                                              \
  SL_using_m operator SL_remove_parenthesis( op )( Oprand&& fs ) SL_expr_equiv( lambda {                               \
    [fs{ std::forward< Oprand >( fs ) }]< class Self, class... Ts >( this Self&& self, Ts&&... args )                  \
        SL_expr_equiv_declval(                                                                                         \
            /*req*/ ( ::short_lambda::function_object::name( SL_forward_like_app( std::declval< Oprand >( ) ) ) ),     \
            ::short_lambda::function_object::name( SL_forward_like_app( fs ) ) )                                       \
  } )

    SL_lambda_unary_operator( negate, ( -) )
    SL_lambda_unary_operator( positate, ( +) )
    SL_lambda_unary_operator( bit_not, ( ~) )
    SL_lambda_unary_operator( logical_not, ( ! ) )
    SL_lambda_unary_operator( address_of, (&) )

#undef SL_lambda_unary_operator

  } // namespace lambda_operators

  template < class CallableT > struct lambda {
    CallableT storage;

    using type   = CallableT;
    using self_t = lambda< CallableT >;

    template < details::similar_to< lambda > Self, class... Ts >
    SL_using_m operator( )( this Self&& self, Ts&&... args )
        SL_expr_equiv( details::forward_like< Self >( self.storage )( std::forward< Ts >( args )... ) )


    template < class Lmb, details::satisfy< operator_with_lambda_enabled, operators_t< operators::then > > RHS >
    SL_using_m then( this Lmb&& lmb, RHS&& rhs ) SL_expr_equiv( ::short_lambda::lambda{
        [ lhs{ std::forward< Lmb >( lmb ) }, rhs{ std::forward< RHS >( rhs ) } ]< class Self, class... Ts >( this Self&& self, Ts&&... args ) noexcept(
            noexcept( SL_forward_like_app( std::declval< Lmb >( ) ) && noexcept(
                SL_forward_like_app( std::declval< RHS >( ) ) ) ) ) -> decltype( auto )
          requires (
              requires { SL_forward_like_app( std::declval< Lmb >( ) ); }
              && requires { SL_forward_like_app( std::declval< RHS >( ) ); } )
        {
          SL_forward_like_app( lhs );
          return SL_forward_like_app( rhs );
        } } )

#define SL_lambda_member_variadic_op( name )                                                                           \
  template < class Lmb, details::satisfy< operator_with_lambda_enabled, operators_t< operators::name > >... RHS >      \
  SL_using_m name( this Lmb&& lmb, RHS&&... rhs ) SL_expr_equiv( ::short_lambda::lambda {                              \
    [lhs{ std::forward< Lmb >( lmb ) },                                                                                \
     ... rhs{ std::forward< RHS >( rhs ) }]< class Self, class... Ts >( Ts&&... args )                                 \
        SL_expr_equiv_declval( ( function_object::name( SL_forward_like_app( std::declval< Lmb >( ) ),                 \
                                                        SL_forward_like_app( std::declval< RHS >( ) )... ) ),          \
                               function_object::name( SL_forward_like_app( lhs ), SL_forward_like_app( rhs )... ) )    \
  } );


    SL_lambda_member_variadic_op( function_call )
    SL_lambda_member_variadic_op( subscript )
#undef SL_lambda_member_variadic_op

#define SL_lambda_member_binary_op_named( name )                                                                       \
  template < class Lmb, details::satisfy< operator_with_lambda_enabled, operators_t< operators::name > > RHS >         \
  SL_using_m name( this Lmb&& lmb, RHS&& rhs ) SL_expr_equiv( ::short_lambda::lambda {                                 \
    [lhs{ std::forward< Lmb >( lmb ) }, rhs{ std::forward< RHS >( rhs ) }]< class Self, class... Ts >( Ts&&... args )  \
        SL_expr_equiv_declval( ( function_object::name( SL_forward_like_app( std::declval< Lmb >( ) ),                 \
                                                        SL_forward_like_app( std::declval< RHS >( ) ) ) ),             \
                               function_object::name( SL_forward_like_app( lhs ), SL_forward_like_app( rhs ) ) )       \
  } );

    SL_lambda_member_binary_op_named( assign_to ) // avoid overloading copy/move assign operator!

#undef SL_lambda_member_binary_op_named

#define SL_lambda_member_binary_op( name, op )                                                                         \
  template < class Lmb, details::satisfy< operator_with_lambda_enabled, operators_t< operators::name > > RHS >         \
  SL_using_m operator SL_remove_parenthesis( op )( this Lmb&& lmb, RHS&& rhs ) SL_expr_equiv( ::short_lambda::lambda { \
    [lhs{ std::forward< Lmb >( lmb ) }, rhs{ std::forward< RHS >( rhs ) }]< class Self, class... Ts >( Ts&&... args )  \
        SL_expr_equiv_declval( ( function_object::name( SL_forward_like_app( std::declval< Lmb >( ) ),                 \
                                                        SL_forward_like_app( std::declval< RHS >( ) ) ) ),             \
                               function_object::name( SL_forward_like_app( lhs ), SL_forward_like_app( rhs ) ) )       \
  } );

    SL_lambda_member_binary_op( add_to, ( += ) )
    SL_lambda_member_binary_op( subtract_from, ( -= ) )
    SL_lambda_member_binary_op( times_by, ( *= ) )
    SL_lambda_member_binary_op( divide_by, ( /= ) )
    SL_lambda_member_binary_op( bit_and_with, ( &= ) )
    SL_lambda_member_binary_op( bit_or_with, ( |= ) )
    SL_lambda_member_binary_op( bit_xor_with, ( ^= ) )
    SL_lambda_member_binary_op( left_shift_with, ( <<= ) )
    SL_lambda_member_binary_op( right_shift_with, ( >>= ) )

#undef SL_lambda_member_binary_op

#define SL_lambda_member_cast_op_named( name )                                                                         \
  template < class Target, class Lmb >                                                                                 \
  SL_using_m name( this Lmb&& lmb, std::type_identity< Target > = { } ) SL_expr_equiv( ::short_lambda::lambda {        \
    [lhs{ std::forward< Lmb >( lmb ) }]< class Self, class... Ts >( Ts&&... args ) SL_expr_equiv_declval(              \
        ( function_object::name( SL_forward_like_app( std::declval< Lmb >( ) ), std::type_identity< Target >{ } ) ),   \
        function_object::name( SL_forward_like_app( lhs ), std::type_identity< Target >{ } ) )                         \
  } );

    SL_lambda_member_cast_op_named( const_cast_ )
    SL_lambda_member_cast_op_named( static_cast_ )
    SL_lambda_member_cast_op_named( dynamic_cast_ )
    SL_lambda_member_cast_op_named( reinterpret_cast_ )
    SL_lambda_member_cast_op_named( cstyle_cast )

#undef SL_lambda_member_cast_op_named

#define SL_lambda_member_unary_op_named( name )                                                                        \
  template < class Lmb >                                                                                               \
  SL_using_m name( this Lmb&& lmb ) SL_expr_equiv( ::short_lambda::lambda {                                            \
    [lhs{ std::forward< Lmb >( lmb ) }]< class Self, class... Ts >( Ts&&... args )                                     \
        SL_expr_equiv_declval( ( function_object::name( SL_forward_like_app( std::declval< Lmb >( ) ) ) ),             \
                               function_object::name( SL_forward_like_app( lhs ) ) )                                   \
  } );

    SL_lambda_member_unary_op_named( throw_ )
    SL_lambda_member_unary_op_named( typeid_ )
    SL_lambda_member_unary_op_named( sizeof_ )
    SL_lambda_member_unary_op_named( alignof_ )
    SL_lambda_member_unary_op_named( co_await_ )

#undef SL_lambda_member_unary_op_named

    template < bool Id = false, class Lmb >
    SL_using_m decltype_( this Lmb&& lmb ) SL_expr_equiv( ::short_lambda::lambda {
      [lhs{ std::forward< Lmb >( lmb ) }]< class Self, class... Ts >( Ts&&... args ) SL_expr_equiv_declval(
          ( function_object::decltype_( SL_forward_like_app( std::declval< Lmb >( ) ),
                                        std::integral_constant< bool, Id >{ } ) ),
          function_object::decltype_( SL_forward_like_app( lhs ), std::integral_constant< bool, Id >{ } ) )
    } );

    template < class Lmb >
    SL_using_m noexcept_( this Lmb&& lmb ) SL_expr_equiv( ::short_lambda::lambda {
      [lhs{ std::forward< Lmb >( lmb ) }]< class Self, class... Ts >( Ts&&... args )
          SL_expr_equiv_declval( ( noexcept( SL_forward_like_app( std::declval< Lmb >( ) ) ) ),
                                 noexcept( SL_forward_like_app( lmb ) ) )
    } );

    template < class Lmb >
    SL_using_m operator++( this Lmb&& lmb ) SL_expr_equiv( ::short_lambda::lambda {
      [lhs{ std::forward< Lmb >( lmb ) }]< class Self, class... Ts >( Ts&&... args )
          SL_expr_equiv_declval( ( function_object::pre_increment( SL_forward_like_app( std::declval< Lmb >( ) ) ) ),
                                 function_object::pre_increment( SL_forward_like_app( lhs ) ) )
    } );
    template < class Lmb >
    SL_using_m operator++( this Lmb&& lmb, int ) SL_expr_equiv( ::short_lambda::lambda {
      [lhs{ std::forward< Lmb >( lmb ) }]< class Self, class... Ts >( Ts&&... args )
          SL_expr_equiv_declval( ( function_object::post_increment( SL_forward_like_app( std::declval< Lmb >( ) ) ) ),
                                 function_object::post_increment( SL_forward_like_app( lhs ) ) )
    } );
    template < class Lmb >
    SL_using_m operator--( this Lmb&& lmb ) SL_expr_equiv( ::short_lambda::lambda {
      [lhs{ std::forward< Lmb >( lmb ) }]< class Self, class... Ts >( Ts&&... args )
          SL_expr_equiv_declval( ( function_object::pre_decrement( SL_forward_like_app( std::declval< Lmb >( ) ) ) ),
                                 function_object::pre_decrement( SL_forward_like_app( lhs ) ) )
    } );
    template < class Lmb >
    SL_using_m operator--( this Lmb&& lmb, int ) SL_expr_equiv( ::short_lambda::lambda {
      [lhs{ std::forward< Lmb >( lmb ) }]< class Self, class... Ts >( Ts&&... args )
          SL_expr_equiv_declval( ( function_object::post_decrement( SL_forward_like_app( std::declval< Lmb >( ) ) ) ),
                                 function_object::post_decrement( SL_forward_like_app( lhs ) ) )
    } );

    template < class Lmb,
               details::satisfy< operator_with_lambda_enabled, operators_t< operators::conditional > > TB,
               details::satisfy< operator_with_lambda_enabled, operators_t< operators::conditional > > FB >
    SL_using_m conditional( this Lmb&& lmb, TB&& tb, FB&& fb ) SL_expr_equiv( ::short_lambda::lambda {
      [lhs{ std::forward< Lmb >( lmb ) },
       tb{ std::forward< TB >( tb ) },
       fb{ std::forward< FB >( fb ) }]< class Self, class... Ts >( Ts&&... args )
          SL_expr_equiv_declval( ( function_object::conditional( SL_forward_like_app( std::declval< Lmb >( ) ),
                                                                 SL_forward_like_app( std::declval< TB >( ) ),
                                                                 SL_forward_like_app( std::declval< FB >( ) ) ) ),
                                 function_object::conditional( SL_forward_like_app( lhs ),
                                                               SL_forward_like_app( tb ),
                                                               SL_forward_like_app( fb ) ) )
    } );

    template < class Lmb >
    SL_using_m operator*( this Lmb&& lmb ) SL_expr_equiv( ::short_lambda::lambda {
      [lhs{ std::forward< Lmb >( lmb ) }]< class Self, class... Ts >( Ts&&... args )
          SL_expr_equiv_declval( ( function_object::indirection( SL_forward_like_app( std::declval< Lmb >( ) ) ) ),
                                 function_object::indirection( SL_forward_like_app( lhs ) ) )
    } );

    template < class Lmb >
    SL_using_m operator->( this Lmb&& lmb ) SL_expr_equiv( ::short_lambda::lambda {
      [lhs{ std::forward< Lmb >( lmb ) }]< class Self, class... Ts >( Ts&&... args ) SL_expr_equiv_declval(
          ( function_object::object_member_access_of_pointer( SL_forward_like_app( std::declval< Lmb >( ) ) ) ),
          function_object::object_member_access_of_pointer( SL_forward_like_app( lhs ) ) )
    } );

    template < class Lmb,
               details::satisfy< operator_with_lambda_enabled, operators_t< operators::pointer_member_access > > Mptr >
    SL_using_m pointer_member_access( this Lmb&& lmb, Mptr&& mptr ) SL_expr_equiv( ::short_lambda::lambda {
      [lhs{ std::forward< Lmb >( lmb ) },
       mptr{ std::forward< Mptr >( mptr ) }]< class Self, class... Ts >( Ts&&... args )
          SL_expr_equiv_declval(
              ( function_object::pointer_member_access( SL_forward_like_app( std::declval< Lmb >( ) ),
                                                        SL_forward_like_app( std::declval< Mptr >( ) ) ) ),
              function_object::pointer_member_access( SL_forward_like_app( lhs ), SL_forward_like_app( mptr ) ) )
    } );

    template < class T, details::satisfy< operator_with_lambda_enabled, operators_t< operators::new_ > >... Args >
      requires ( std::same_as< Args, self_t > || ... )
    SL_using_f new_( Args&&... args1 ) SL_expr_equiv(
        [... args1{ std::forward< Args >( args1 ) }]< class Self, class... Ts >( Ts&&... args ) SL_expr_equiv_declval(
            ( function_object::new_( std::type_identity< T >{ }, SL_forward_like_app( std::declval< Args >( ) )... ) ),
            function_object::new_( std::type_identity< T >{ }, SL_forward_like_app( args1 )... ) ) )

    template < bool Array = false, class Lmb >
    SL_using_m delete_( this Lmb&& lmb ) SL_expr_equiv( ::short_lambda::lambda {
      [lhs{ std::forward< Lmb >( lmb ) }]< class Self, class... Ts >( Ts&&... args ) SL_expr_equiv_declval(
          ( function_object::delete_( SL_forward_like_app( std::declval< Lmb >( ) ),
                                      std::integral_constant< bool, Array >{ } ) ),
          function_object::delete_( SL_forward_like_app( lhs ), std::integral_constant< bool, Array >{ } ) )
    } );
  };

  inline namespace factory {
    template < std::size_t idx > struct projector_t {
      template < class... Ts >
      constexpr inline static bool construct_from_input
          = ! std::is_reference_v< std::tuple_element_t< idx, std::tuple< Ts... > > >;


      template < class... Ts >
        requires ( sizeof...( Ts ) > idx )
      constexpr static
          typename std::conditional_t< construct_from_input< Ts... >,
                                       std::remove_cvref_t< std::tuple_element_t< idx, std::tuple< Ts... > > >,
                                       std::tuple_element_t< idx, std::tuple< Ts... > > >
          operator( )( Ts&&... args )
              SL_expr_equiv_no_ret( std::get< idx >( std::tuple< Ts... >{ std::forward< Ts >( args )... } ) )
    };

    struct lift_t { // forwarding construct received argument
      template < class T > SL_using_v noexcept_of( ) {
        if constexpr ( std::is_reference_v< T > ) {
          return noexcept(
              lambda{ [ v = std::addressof( std::declval< T >( ) ) ]< class Self, class... Ts >(
                          this Self&& self,
                          Ts&&... args ) noexcept -> decltype( auto ) { return static_cast< T >( *v ); } } );
        } else {
          return noexcept( lambda{
              [ v{ std::declval< T& >( ) } ]< class Self, class... Ts >( this Self&& self, Ts&&... args ) -> auto {
                return v;
              } } );
        }
      }

      template < class T > SL_using_v constraint_of( ) {
        if constexpr ( std::is_reference_v< T > ) {
          return requires {
                   lambda{ [ v = std::addressof( std::declval< T >( ) ) ]< class Self, class... Ts >(
                               this Self&& self,
                               Ts&&... args ) noexcept -> decltype( auto ) { return static_cast< T >( *v ); } };
                 };
        } else {
          return requires {
                   lambda{ [ v{ std::declval< T& >( ) } ]< class Self, class... Ts >( this Self&& self,
                                                                                      Ts&&... args ) -> auto {
                     return v;
                   } };
                 };
        }
      }

      template < class T >
      SL_using_v operator( )( T&& value ) noexcept( noexcept_of< T >( ) )
          ->decltype( auto )
        requires ( constraint_of< T >( ) )
      {
        if constexpr ( std::is_reference_v< T > ) { // lvalue ref
          return lambda{ [ v = std::addressof( value ) ]< class Self, class... Ts >(
                             this Self&& self,
                             Ts&&... args ) noexcept -> decltype( auto ) { return static_cast< T >( *v ); } };
        } else {
          return lambda{
              [ v{ std::forward< T >( value ) } ]< class Self, class... Ts >( this Self&& self, Ts&&... args ) -> auto {
                return v;
              } };
        }
      }
    };


    SL_using_v $0 = lambda{ projector_t< 0 >{} };
    SL_using_v $1 = lambda{ projector_t< 1 >{} };
    SL_using_v $2 = lambda{ projector_t< 2 >{} };
    SL_using_v $3 = lambda{ projector_t< 3 >{} };
    SL_using_v $4 = lambda{ projector_t< 4 >{} };
    SL_using_v $5 = lambda{ projector_t< 5 >{} };
    SL_using_v $6 = lambda{ projector_t< 6 >{} };
    SL_using_v $7 = lambda{ projector_t< 7 >{} };
    SL_using_v $8 = lambda{ projector_t< 8 >{} };
    SL_using_v $9 = lambda{ projector_t< 9 >{} };
    SL_using_v $_ = lift_t{ };

    template < class U > struct coprojector_t {
      template < class T > SL_using_v operator( )( T&& arg ) SL_expr_equiv( $_( static_cast< U& >( arg ) ) )
    };

    template < class T >
      requires std::is_default_constructible_v< T >
    struct storage_t {
      T value;

      template < class U, class Self >
      constexpr operator U&( this Self&& self ) SL_expr_equiv_no_ret( details::forward_like< Self >( self.value ) )

      template < class... Ts, class Self >
      SL_using_m operator( )( this Self&& self, Ts&&... args )
          SL_expr_equiv( details::forward_like< Self >( self.value ) )
    };


    template < class T, std::size_t id = 0 > inline static storage_t< T > storage{ };

    template < class U, std::size_t id = 0 > SL_using_v _$ = coprojector_t< U >{ }( storage< U, id > );

  } // namespace factory

} // namespace short_lambda


#undef SL_expr_equiv
#undef SL_expr_equiv_declval
#undef SL_expr_equiv_bare
#undef SL_expr_equiv_no_ret

#undef SL_forward_like_app
#undef SL_remove_parenthesis_1
#undef SL_remove_parenthesis_0
#undef SL_remove_parenthesis

#undef SL_using_v
#undef SL_using_m
#undef SL_using_st
#undef SL_using_f
