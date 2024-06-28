#pragma once

#include <cstddef>
#include <memory>
#include <tuple>
#include <type_traits>
#include <utility>

namespace short_lambda::details {
  template < class T, class U >
  concept similar_to = std::same_as< U, std::remove_cvref_t< T > >;

  template < class T, template < class... > class U, class... Us >
  concept satisfy = U< std::remove_cvref_t< T >, Us... >::value;

  template < template < class > class U, class... Ts >
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

#define SL_one_liner_bare( ... )                                                                                       \
  { return ( __VA_ARGS__ ); } // extra parenthesis for decltype(auto)

#define SL_one_liner( ... )                                                                                            \
  noexcept( noexcept( __VA_ARGS__ ) )                                                                                  \
      ->decltype( auto )                                                                                               \
    requires requires { __VA_ARGS__; }                                                                                 \
  SL_one_liner_bare( __VA_ARGS__ )

#define SL_one_liner_no_ret( ... )                                                                                     \
  noexcept( noexcept( __VA_ARGS__ ) )                                                                                  \
    requires requires { __VA_ARGS__; }                                                                                 \
  SL_one_liner_bare( __VA_ARGS__ )

#define SL_one_liner_declval( req, ... )                                                                               \
  noexcept( noexcept( req ) )                                                                                          \
      ->decltype( auto )                                                                                               \
    requires requires { req; }                                                                                         \
  SL_one_liner_bare( __VA_ARGS__ )

#define SL_forward_like_app( ... )     details::forward_like< Self >( __VA_ARGS__ )( std::forward< Ts >( args )... )
#define SL_remove_parenthesis_1( ... ) __VA_ARGS__
#define SL_remove_parenthesis_0( X )   X
#define SL_remove_parenthesis( X )     SL_remove_parenthesis_0( SL_remove_parenthesis_1 X )


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
    object_member_access,
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
    new_,
    delete_,
    co_await_ = 59, // ^ special
  };

  template < operators op > struct operators_t {
    [[maybe_unused]] static inline constexpr operators value = op;
  };

  template < class T > struct is_operators_t: std::false_type { };

  template < operators op > struct is_operators_t< operators_t< op > >: std::true_type { };

  template < class T > struct every_operator_with_lambda_enabled: std::false_type { };

  template < details::satisfy< is_short_lambda > lambdaT >
  struct every_operator_with_lambda_enabled< lambdaT >: std::true_type { };

  template < class T, details::satisfy< is_operators_t > OpT > struct operator_with_lambda_enabled: std::false_type { };

  template < details::satisfy< every_operator_with_lambda_enabled > T, details::satisfy< is_operators_t > OpT >
  struct operator_with_lambda_enabled< T, OpT >: std::true_type { };

  inline namespace function_object {

#define SL_define_binary_op( name, op )                                                                                \
  struct name##_t {                                                                                                    \
    template < class LHS, class RHS >                                                                                  \
    constexpr static auto operator( )( LHS&& lhs, RHS&& rhs )                                                          \
        SL_one_liner( std::forward< LHS >( lhs ) SL_remove_parenthesis( op ) std::forward< RHS >( rhs ) )              \
  } constexpr static inline name{ };

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
#undef SL_define_binary_op // undefine


#define SL_define_unary_op( name, op )                                                                                 \
  struct name##_t {                                                                                                    \
    template < class Oprand >                                                                                          \
    constexpr static auto operator( )( Oprand&& arg )                                                                  \
        SL_one_liner( SL_remove_parenthesis( op ) std::forward< Oprand >( arg ) )                                      \
  } constexpr static inline name{ };

    SL_define_unary_op( negate, ( -) )
    SL_define_unary_op( positate, ( +) )
    SL_define_unary_op( bit_not, ( ~) )
    SL_define_unary_op( logical_not, ( ! ) )
    SL_define_unary_op( address_of, (&) )
    SL_define_unary_op( indiraction, (*) )

#undef SL_define_unary_op

#define SL_define_unary_member_op( name, op )                                                                          \
  struct name##_t {                                                                                                    \
    template < class Oprand >                                                                                          \
    constexpr static auto operator( )( Oprand&& arg )                                                                  \
        SL_one_liner( std::forward< Oprand >( arg ).operator SL_remove_parenthesis( op )( ) )                          \
  } constexpr static inline name{ };

    SL_define_unary_member_op( object_member_access_of_pointer, (->) )

#undef SL_define_unary_member_op

    // some unoverloadable operator

    struct pointer_member_access_t { // a.*b
      template < class LHS, class RHS >
      constexpr static auto operator( )( LHS&& lhs, RHS&& rhs )
          SL_one_liner( std::forward< LHS >( lhs ).*( std::forward< RHS >( rhs ) ) )
    } constexpr static inline pointer_member_access{ };

    // It seems that it's impossible to implement object_member_access (a.k.a. `dot') operator.


  } // namespace function_object

  inline namespace lambda_operators {
#define SL_lambda_binary_operator( name, op )                                                                          \
  template < details::satisfy< operator_with_lambda_enabled, operators_t< operators::name > > LHS,                     \
             details::satisfy< operator_with_lambda_enabled, operators_t< operators::name > > RHS >                    \
    requires details::any_satisfy< is_short_lambda, LHS, RHS >                                                         \
  auto operator SL_remove_parenthesis( op )( LHS&& lhs, RHS&& rhs ) SL_one_liner( lambda {                             \
    [lhs{ std::forward< LHS >( lhs ) },                                                                                \
     rhs{ std::forward< RHS >( rhs ) }]< class Self, class... Ts >( this Self&& self, Ts&&... args )                   \
        SL_one_liner_declval( /*req*/ ( name( SL_forward_like_app( std::declval< LHS >( ) ),                           \
                                              SL_forward_like_app( std::declval< RHS >( ) ) ) ),                       \
                              name( SL_forward_like_app( lhs ), SL_forward_like_app( rhs ) ) )                         \
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

#undef SL_lambda_binary_operator


#define SL_lambda_unary_operator( name, op )                                                                           \
  template < details::satisfy< is_short_lambda > Oprand >                                                              \
  auto operator SL_remove_parenthesis( op )( Oprand&& fs ) SL_one_liner( lambda {                                      \
    [fs{ std::forward< Oprand >( fs ) }]< class Self, class... Ts >( this Self&& self, Ts&&... args )                  \
        SL_one_liner_declval( /*req*/ ( name( SL_forward_like_app( std::declval< Oprand >( ) ) ) ),                    \
                              name( SL_forward_like_app( fs ) ) )                                                      \
  } )

    SL_lambda_unary_operator( negate, ( -) )
    SL_lambda_unary_operator( positate, ( +) )
    SL_lambda_unary_operator( bit_not, ( ~) )
    SL_lambda_unary_operator( logical_not, ( ! ) )

#undef SL_lambda_unary_operator

  } // namespace lambda_operators

  template < class CallableT > struct lambda {
    CallableT storage;

    using type = CallableT;

    template < details::similar_to< lambda > Self, class... Ts >
    [[maybe_unused]] constexpr auto operator( )( this Self&& self, Ts&&... args )
        SL_one_liner( details::forward_like< Self >( self.storage )( std::forward< Ts >( args )... ) )
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
              SL_one_liner_no_ret( std::get< idx >( std::tuple< Ts... >{ std::forward< Ts >( args )... } ) )
    };

    struct lift_t { // forwarding construct received argument
      template < class T > constexpr static auto noexcept_of( ) {
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

      template < class T > constexpr static auto constraint_of( ) {
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
      constexpr static auto operator( )( T&& value ) noexcept( noexcept_of< T >( ) )
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

    [[maybe_unused]] static constexpr inline auto $0 = lambda{ projector_t< 0 >{} };
    [[maybe_unused]] static constexpr inline auto $1 = lambda{ projector_t< 1 >{} };
    [[maybe_unused]] static constexpr inline auto $2 = lambda{ projector_t< 2 >{} };
    [[maybe_unused]] static constexpr inline auto $3 = lambda{ projector_t< 3 >{} };
    [[maybe_unused]] static constexpr inline auto $4 = lambda{ projector_t< 4 >{} };
    [[maybe_unused]] static constexpr inline auto $5 = lambda{ projector_t< 5 >{} };
    [[maybe_unused]] static constexpr inline auto $6 = lambda{ projector_t< 6 >{} };
    [[maybe_unused]] static constexpr inline auto $7 = lambda{ projector_t< 7 >{} };
    [[maybe_unused]] static constexpr inline auto $8 = lambda{ projector_t< 8 >{} };
    [[maybe_unused]] static constexpr inline auto $9 = lambda{ projector_t< 9 >{} };
    [[maybe_unused]] static constexpr inline auto $_ = lift_t{ };

  } // namespace factory

} // namespace short_lambda


#undef SL_one_liner
#undef SL_one_liner_declval
#undef SL_one_liner_bare
#undef SL_one_liner_no_ret

#undef SL_forward_like_app
#undef SL_remove_parenthesis_1
#undef SL_remove_parenthesis_0
#undef SL_remove_parenthesis
