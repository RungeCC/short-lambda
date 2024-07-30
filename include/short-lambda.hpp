#pragma once

#if defined( _MSC_VER )
#  define SL_cxx_msvc
#elif defined( __clang__ )
#  define SL_cxx_clang
#elif defined( __GNUC__ )
#  define SL_cxx_gcc
#elif
static_assert( false, "unsupported compiler" );
#endif

#if defined( __RESHARPER__ )
#  define SL_anal_resharper
#elif defined( __INTELLISENSE__ )
#  define SL_anal_intellisense
#elif defined( __clangd__ )
#  define SL_anal_clangd
#endif

#include <memory> // for std::addressof
#include <tuple>  // for std::tuple, std::tuple_size, std::tuple_element, std::get(std::tuple)
#include <type_traits> // for type_traits, std::integral_constant, std::bool_constant, std::true_type, std::false_type
#include <typeindex> // for std::type_index, typeid
#include <utility> // for std::forward, std::move, std::as_const, std::declval, std::integer_sequence, std::make_integer_sequence , std::index_sequence_for

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

#define SL_forward_like_app( ... )                                                                 \
  details::forward_like< Self >( __VA_ARGS__ )( std::forward< Ts >( args )... )
#define SL_remove_parenthesis_1( ... ) __VA_ARGS__
#define SL_remove_parenthesis_0( X )   X
#define SL_remove_parenthesis( X )     SL_remove_parenthesis_0( SL_remove_parenthesis_1 X )

#define SL_using_st( name )            static constexpr inline name [[maybe_unused]]
#if not defined( __cpp_static_call_operator )
/// @note: msvc currently does not support `static operator()`, so we need a feature test macro here
#  define SL_using_c [[maybe_unused]] constexpr inline auto
#else
#  define SL_using_c [[maybe_unused]] static constexpr inline auto
#endif
#define SL_using_v [[maybe_unused]] static constexpr inline auto
#define SL_using_m [[maybe_unused]] constexpr inline auto
#define SL_using_f [[maybe_unused]] friend constexpr inline auto

#if defined( __cpp_static_call_operator )
#  define SL_using_paren( ... )                                                                    \
    [[maybe_unused]] static constexpr inline auto operator( )( __VA_ARGS__ )
#else
#  define SL_using_paren( ... )                                                                    \
    [[maybe_unused]] constexpr inline auto operator( )( __VA_ARGS__ ) const
#endif

#if not defined( __cpp_auto_cast )
/// @note: we use list-initialization but not non-list-direct-initialization to avoid some unwanted
/// conversions
#  define SL_decay_copy( ... )                                                                     \
    std::decay_t< decltype( ( __VA_ARGS__ ) ) > { __VA_ARGS__ }
#else
#  define SL_decay_copy( ... )                                                                     \
    auto { __VA_ARGS__ }
#endif

namespace short_lambda::details {
  using size_t = decltype( sizeof( 0 ) ); // avoid including cstddef header file

  template < class T, class U, class... >
  concept uncvref_same_as = std::same_as< std::remove_cvref_t< U >, std::remove_cvref_t< T > >;

  template < class T, template < class... > class U, class... Us >
  concept satisfy = U< std::remove_cvref_t< T >, Us... >::value;

  template < template < class... > class U, class... Ts >
  concept any_satisfy = ( U< std::remove_cvref_t< Ts > >::value || ... );

  template < template < class... > class U, class... Ts >
  concept all_satisfy = ( U< std::remove_cvref_t< Ts > >::value && ... );

  template < template < class... > class U, class... Ts >
  struct is_first_satisfy: std::false_type { };

  template < template < class... > class U, class A, class... Ts >
  struct is_first_satisfy< U, A, Ts... >: std::bool_constant< U< A >::value > { };

  template < template < class... > class U, class... Ts >
  concept first_satisfy = is_first_satisfy< U, Ts... >::value;

  template < class... > struct is_same: std::false_type { };

  template < class A, class... Ts > struct is_same< A, A, Ts... >: std::true_type { };

  template < template < class... > class U, class... Ts > struct lpartial {
    template < class... Us > using type = U< Ts..., Us... >;
  };

  template < class T, class U > constexpr auto&& forward_like( U&& x ) noexcept {
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
  /// @note: function object demux :: (As... -> R) -> ((Us... -> As)...) -> Us... -> R
  struct demux_t {
    template < class Fn, class... Slots >
    SL_using_paren( Fn&& fn, Slots&&... slots )
        noexcept( noexcept( (void) SL_decay_copy( fn ), ( (void) SL_decay_copy( slots ), ... ) ) )
            ->decltype( auto )
      requires requires {
        (void) SL_decay_copy( fn );
        ( (void) SL_decay_copy( slots ), ... );
      }
    {
      return [ fn{ std::forward< Fn >( fn ) },
               ... slots{ std::forward< Slots >(
                   slots ) } ]< class Self, class... Args >( this Self&&, Args&&... args )
                 SL_expr_equiv_spec( forward_like< Self >( std::declval< Fn >( ) )(
                     details::forward_like< Self >( std::declval< Slots >( ) )(
                         std::forward< Args >( args )... )... ) ) {
                   return details::forward_like< Self >( fn )( details::forward_like< Self >(
                       slots )( std::forward< Args >( args )... )... );
                 };
    }
  } SL_using_st( demux ){ };

  struct bind_front_t {
    template < class Fn, class... Binds >
    SL_using_paren( Fn&& fn, Binds&&... binds )
        noexcept( noexcept( (void) SL_decay_copy( fn ), ( (void) SL_decay_copy( binds ), ... ) ) )
            ->decltype( auto )
      requires requires {
        (void) SL_decay_copy( fn );
        ( (void) SL_decay_copy( binds ), ... );
      }
    {
      return [ fn{ std::forward< Fn >( fn ) },
               ... binds{ std::forward< Binds >(
                   binds ) } ]< class Self, class... Args >( this Self&&, Args&&... args )
                 SL_expr_equiv_spec( forward_like< Self >( std::declval< Fn >( ) )(
                     details::forward_like< Self >( std::declval< Binds >( ) )...,
                     std::forward< Args >( args )... ) ) {
                   return details::forward_like< Self >( fn )(
                       details::forward_like< Self >( binds )...,
                       std::forward< Args >( args )... );
                 };
    }
  } SL_using_st( bind_front ){ };

  struct bind_back_t {
    template < class Fn, class... Binds >
    SL_using_paren( Fn&& fn, Binds&&... binds )
        noexcept( noexcept( (void) SL_decay_copy( fn ), ( (void) SL_decay_copy( binds ), ... ) ) )
            ->decltype( auto )
      requires requires {
        (void) SL_decay_copy( fn );
        ( (void) SL_decay_copy( binds ), ... );
      }
    {
      return [ fn{ std::forward< Fn >( fn ) },
               ... binds{ std::forward< Binds >(
                   binds ) } ]< class Self, class... Args >( this Self&&, Args&&... args )
                 SL_expr_equiv_spec( details::forward_like< Self >( std::declval< Fn >( ) )(
                     std::forward< Args >( args )...,
                     details::forward_like< Self >( std::declval< Binds >( ) )... ) ) {
                   return details::forward_like< Self >( fn )(
                       std::forward< Args >( args )...,
                       details::forward_like< Self >( binds )... );
                 };
    }
  } SL_using_st( bind_back ){ };

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
    typeof_,        // typeof_(x) := decltype((x)), they are c23 keywords, so we add a _ suffix
    typeof_unqual_  // typeof_unqual_(x) := std::remove_cvref_t<decltype((x))>
  };

  template < operators op > struct operators_t {
    SL_using_v value = op;
  };

  template < class T > struct is_operators_t: std::false_type { };

  template < operators op > struct is_operators_t< operators_t< op > >: std::true_type { };

  template < class T > struct every_operator_with_lambda_enabled: std::false_type { };

  template < details::satisfy< is_short_lambda > lambdaT >
  struct every_operator_with_lambda_enabled< lambdaT >: std::true_type { };

  template < class T, details::satisfy< is_operators_t > OpT >
  struct operator_with_lambda_enabled: std::false_type { };

  template < details::satisfy< every_operator_with_lambda_enabled > T,
             details::satisfy< is_operators_t >                     OpT >
  struct operator_with_lambda_enabled< T, OpT >: std::true_type { };

  namespace function_object {

#define SL_define_binary_op( name, op )                                                            \
  struct name##_t {                                                                                \
    template < class LHS, class RHS >                                                              \
    SL_using_paren( LHS&& lhs, RHS&& rhs ) SL_expr_equiv(                                          \
        std::forward< LHS >( lhs ) SL_remove_parenthesis( op ) std::forward< RHS >( rhs ) )        \
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

#define SL_define_unary_op( name, op )                                                             \
  struct name##_t {                                                                                \
    template < class Operand >                                                                     \
    SL_using_paren( Operand&& arg )                                                                \
        SL_expr_equiv( SL_remove_parenthesis( op ) std::forward< Operand >( arg ) )                \
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
      template < class Operand >
      SL_using_paren( Operand&& arg ) SL_expr_equiv( std::forward< Operand >( arg )-- )
    } SL_using_st( post_increment ){ };

    struct post_decrement_t {
      template < class Operand >
      SL_using_paren( Operand&& arg ) SL_expr_equiv( std::forward< Operand >( arg )-- )
    } SL_using_st( post_decrement ){ };

    struct object_member_access_of_pointer_t {
      template < class Operand >
      SL_using_paren( Operand&& arg ) SL_expr_equiv( std::forward< Operand >( arg ).operator->( ) )
    } SL_using_st( object_member_access_of_pointer ){ };

    // some un-overloadable operator
    struct pointer_member_access_t { // a.*b
      template < class LHS, class RHS >
      SL_using_paren( LHS&& lhs, RHS&& rhs )
          SL_expr_equiv( std::forward< LHS >( lhs ).*( std::forward< RHS >( rhs ) ) )
    } SL_using_st( pointer_member_access ){ };

    // It seems that it's impossible to implement object_member_access (a.k.a. `dot') operator.

    struct function_call_t {
      template < class F, class... Args >
      SL_using_paren( F&& f, Args&&... args )
          SL_expr_equiv( std::forward< F >( f )( std::forward< Args >( args )... ) )
    } SL_using_st( function_call ){ };

#if not ( defined( SL_cxx_msvc ) or defined( SL_anal_resharper ) )
    /// @note: msvc does not support multiple index subscript operator
    ///        resharper++ obeys msvc's prefer.
    struct subscript_t {
      template < class Array, class... Idx >
      SL_using_paren( Array&& arr, Idx&&... idx )
          SL_expr_equiv( std::forward< Array >( arr )[ std::forward< Idx >( idx )... ] )
    } SL_using_st( subscript ){ };
#else
    struct subscript_t {
      template < class Array, class Idx >
      SL_using_paren( Array&& arr, Idx&& idx )
          SL_expr_equiv( std::forward< Array >( arr )[ std::forward< Idx >( idx ) ] )
    } SL_using_st( subscript ){ };
#endif

    struct conditional_t {
      template < class Cond, class TrueB, class FalseB >
      SL_using_paren( Cond&& cond, TrueB&& trueb, FalseB&& falseb )
          SL_expr_equiv( std::forward< Cond >( cond ) ? std::forward< TrueB >( trueb )
                                                      : std::forward< FalseB >( falseb ) )
    } SL_using_st( conditional ){ };

    struct static_cast_t {
      template < class Target, class Op >
      SL_using_paren( Op&& arg, std::type_identity< Target > = { } )
          SL_expr_equiv( static_cast< Target >( std::forward< Op >( arg ) ) )
    } SL_using_st( static_cast_ ){ };

    struct const_cast_t {
      template < class Target, class Op >
      SL_using_paren( Op&& arg, std::type_identity< Target > = { } )
          SL_expr_equiv( const_cast< Target >( std::forward< Op >( arg ) ) )
    } SL_using_st( const_cast_ ){ };

    struct dynamic_cast_t {
      template < class Target, class Op >
      SL_using_paren( Op&& arg, std::type_identity< Target > = { } )
          SL_expr_equiv( dynamic_cast< Target >( std::forward< Op >( arg ) ) )
    } SL_using_st( dynamic_cast_ ){ };

    struct reinterpret_cast_t {
      template < class Target, class Op >
      SL_using_paren( Op&& arg, std::type_identity< Target > = { } )
          SL_expr_equiv( reinterpret_cast< Target >( std::forward< Op >( arg ) ) )
    } SL_using_st( reinterpret_cast_ ){ };

    struct cstyle_cast_t {
      template < class Target, class Op >
      SL_using_paren( Op&& arg, std::type_identity< Target > = { } )
          SL_expr_equiv( (Target) ( std::forward< Op >( arg ) ) )
    } SL_using_st( cstyle_cast ){ };

    struct throw_t {
#if defined( __cpp_static_call_operator )
      template < class Op >
      /*constexpr*/ [[noreturn]] static auto operator( )( Op&& arg ) noexcept( false ) -> void
        requires requires { SL_decay_copy( std::forward< Op >( arg ) ); }
      {
        throw std::forward< Op >( arg );
      }
#else
      template < class Op >
      /*constexpr*/ [[noreturn]] auto operator( )( Op&& arg ) const noexcept( false ) -> void
        requires requires { SL_decay_copy( std::forward< Op >( arg ) ); }
      {
        throw std::forward< Op >( arg );
      }
#endif
    } SL_using_st( throw_ ){ };

    struct noexcept_t {
      /// @note: this operator can not work as expected, so we delete it
      template < class Op > SL_using_paren( Op&& arg ) noexcept -> bool = delete;
    } SL_using_st( noexcept_ ){ };

    struct decltype_t {
      template < class Op, bool id = false >
      SL_using_paren( Op&& arg, std::bool_constant< id > = { } ) noexcept
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
      SL_using_paren( Op&& arg ) noexcept
        requires requires { std::type_index{ typeid( arg ) }; }
      {
        return std::type_index{ typeid( arg ) };
      }
    } SL_using_st( typeid_ ){ };

    struct sizeof_t {
      template < class Op >
      SL_using_paren( Op&& arg ) noexcept
        requires requires { sizeof( arg ); }
      {
        return sizeof( arg );
      }
    } SL_using_st( sizeof_ ){ };

    struct alignof_t {
      template < class Op >
      SL_using_paren( Op&& ) noexcept
        requires requires { alignof( std::remove_cvref_t< Op > ); }
      {
        return alignof( std::remove_cvref_t< Op > );
      }
    } SL_using_st( alignof_ ){ };

    struct new_t {
      template < class T0, class... Ts >
      SL_using_paren( std::type_identity< T0 >, Ts&&... args )
          SL_expr_equiv( new T0{ std::forward< Ts >( args )... } )
    } SL_using_st( new_ ){ };

    struct delete_t {
      template < bool Array = false, class Op >
      SL_using_paren( Op&& arg, std::bool_constant< Array > = { } ) noexcept( []( ) {
        if constexpr ( Array ) {
          return noexcept( delete[] arg );
        } else {
          return noexcept( delete arg );
        }
      }( ) )
          ->decltype( auto )
        requires ( []( ) {
          if constexpr ( Array ) {
            return requires { delete[] arg; };
          } else {
            return requires { delete arg; };
          }
        }( ) )
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
      SL_using_paren( Op&& arg )
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
      SL_using_paren( LHS&& lhs, RHS&& rhs )
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

    struct typeof_t {
      template < class Op >
      SL_using_paren( Op&& arg ) SL_expr_equiv( std::type_identity< decltype( ( arg ) ) >{ } )
    } SL_using_st( typeof_ ){ };

    struct typeof_unqual_t {
      template < class Op >
      SL_using_paren( Op&& arg )
          SL_expr_equiv( std::type_identity< std::remove_cvref_t< decltype( ( arg ) ) > >{ } )
    } SL_using_st( typeof_unqual_ ){ };

  } // namespace function_object

  inline namespace factory {
    template < details::size_t idx > struct projector_t {
      template < class... Ts >
      constexpr inline static bool construct_from_input
          = not std::is_lvalue_reference_v< std::tuple_element_t< idx, std::tuple< Ts&&... > > >;

#if defined( __cpp_static_call_operator )
      template < class... Ts >
        requires ( sizeof...( Ts ) > idx )
      constexpr static typename std::conditional_t<
          construct_from_input< Ts... >,
          std::remove_cvref_t< std::tuple_element_t< idx, std::tuple< Ts... > > >,
          std::tuple_element_t< idx, std::tuple< Ts&&... > > >
      operator( )( Ts&&... args ) SL_expr_equiv_no_ret(
          std::get< idx >( std::tuple< Ts... >{ std::forward< Ts >( args )... } ) )
#else
      template < class... Ts >
        requires ( sizeof...( Ts ) > idx )
      constexpr typename std::conditional_t<
          construct_from_input< Ts... >,
          std::remove_cvref_t< std::tuple_element_t< idx, std::tuple< Ts... > > >,
          std::tuple_element_t< idx, std::tuple< Ts&&... > > >
      operator( )( Ts&&... args ) const SL_expr_equiv_no_ret(
          std::get< idx >( std::tuple< Ts... >{ std::forward< Ts >( args )... } ) )
#endif
    };

    template < template < class > class Target >
    struct lift_t { // forwarding construct received argument
      template < class T > static bool consteval inline constraint_of( ) noexcept {
        if constexpr ( std::is_lvalue_reference_v< T&& > ) {
          return requires {
            ( Target{ [ v = std::addressof( std::declval< T& >( ) ) ]< class Self, class... Ts >(
                          [[maybe_unused]] this Self&& self,
                          [[maybe_unused]] Ts&&... args ) noexcept -> decltype( auto ) {
              return static_cast< T >( *v );
            } } );
          };
        } else {
          return requires {
            ( Target{
                [ v{ std::declval< T& >( ) } ]< class Self, class... Ts >(
                    [[maybe_unused]] this Self&& self,
                    [[maybe_unused]] Ts&&... args ) noexcept( noexcept( SL_decay_copy( std::declval< T& >( ) ) ) )
                    -> auto { return v; } } );
          };
        }
      }
      template < class T > static bool consteval inline noexcept_of( ) noexcept {
        if constexpr ( std::is_lvalue_reference_v< T&& > ) {
          return noexcept(
              Target{ [ v = std::addressof( std::declval< T& >( ) ) ]< class Self, class... Ts >(
                          [[maybe_unused]] this Self&& self,
                          [[maybe_unused]] Ts&&... args ) noexcept -> decltype( auto ) {
                return static_cast< T >( *v );
              } } );
        } else {
          return noexcept( Target{
              [ v{ std::declval< T& >( ) } ]< class Self, class... Ts >(
                  [[maybe_unused]] this Self&& self,
                  [[maybe_unused]] Ts&&... args ) noexcept( noexcept( SL_decay_copy( std::declval< T& >( ) ) ) )
                  -> auto { return v; } } );
        }
      }

      template < class T >
      SL_using_paren( T&& value ) noexcept( noexcept_of< T >( ) )
          ->decltype( auto )
        requires ( constraint_of< T >( ) )
      {
        /// @note: there's a bug in gcc:
        /// [[maybe_unused]] does not have effect here.
        if constexpr ( std::is_lvalue_reference_v< T&& > ) {
          return ( Target{
              [ v = std::addressof( value ) ]< class Self, class... Ts >(
                  [[maybe_unused]] this Self&& self,
                  Ts&&... ) noexcept -> decltype( auto ) { return static_cast< T >( *v ); } } );
        } else {
          return ( Target{
              [ v{ std::forward< T >( value ) } ]< class Self, class... Ts >(
                  [[maybe_unused]] this Self&& self,
                  Ts&&... ) noexcept( noexcept( SL_decay_copy( std::declval< T& >( ) ) ) ) -> auto {
                return v;
              } } );
        }
      }
    };

    template < class T > struct storage_t {
      T value;

      template < class U, class Self >
      constexpr operator U&( [[maybe_unused]] this Self&& self )
          SL_expr_equiv_no_ret( details::forward_like< Self >( self.value ) )

      template < class... Ts, class Self >
      SL_using_m operator( )( [[maybe_unused]] this Self&& self, [[maybe_unused]] Ts&&... args )
          SL_expr_equiv( details::forward_like< Self >( self.value ) )
    };

    template < details::satisfy< std::is_default_constructible > T, details::size_t id = 0 >
    inline storage_t< T > storage{ };

    template < auto value, details::size_t id = 0 >
    SL_using_m constant = storage_t< std::remove_cvref_t< decltype( value ) > const >{ value };

    template < template < class > class Target, class U > struct coprojector_t {
      template < class T >
      SL_using_paren( T&& arg ) SL_expr_equiv( lift_t< Target >{ }( static_cast< U& >( arg ) ) )
    };
  } // namespace factory

  inline namespace lambda_operators {
#define SL_lambda_binary_operator( name, op )                                                       \
  template < details::satisfy< operator_with_lambda_enabled, operators_t< operators::name > > LHS,  \
             details::satisfy< operator_with_lambda_enabled, operators_t< operators::name > > RHS > \
    requires details::any_satisfy< is_short_lambda, LHS, RHS >                                      \
  SL_using_m operator SL_remove_parenthesis( op )( LHS&& lhs, RHS&& rhs )                           \
      SL_expr_equiv( lambda{ details::demux( function_object::name,                                 \
                                             std::forward< LHS >( lhs ),                            \
                                             std::forward< RHS >( rhs ) ) } )

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


#define SL_lambda_unary_operator( name, op )                                                       \
  template < details::satisfy< is_short_lambda > Operand >                                         \
  SL_using_m operator SL_remove_parenthesis( op )( Operand&& fs ) SL_expr_equiv(                   \
      lambda{ details::demux( function_object::name, std::forward< Operand >( fs ) ) } )

    SL_lambda_unary_operator( negate, ( -) )
    SL_lambda_unary_operator( positate, ( +) )
    SL_lambda_unary_operator( bit_not, ( ~) )
    SL_lambda_unary_operator( logical_not, ( ! ) )

#undef SL_lambda_unary_operator

  } // namespace lambda_operators

  template < class CallableT > struct lambda {
    [[maybe_unused]] CallableT storage;

    using type   = CallableT;
    using self_t = lambda< CallableT >;

    template < details::uncvref_same_as< lambda > Self, class... Ts >
    SL_using_m operator( )( [[maybe_unused]] this Self&& self, Ts&&... args ) SL_expr_equiv(
        details::forward_like< Self >( self.storage )( std::forward< Ts >( args )... ) )


    template < class Lmb,
               details::satisfy< operator_with_lambda_enabled, operators_t< operators::then > > RHS >
    SL_using_m then( this Lmb&& lmb, RHS&& rhs ) SL_expr_equiv( ::short_lambda::lambda{
        [ lhs{ std::forward< Lmb >( lmb ) },
          rhs{ std::forward< RHS >( rhs ) } ]< class Self, class... Ts >(
            [[maybe_unused]] this Self&& self,
            Ts&&... args ) noexcept( noexcept( SL_forward_like_app( std::declval< Lmb >( ) ) ) && noexcept( SL_forward_like_app( std::declval< RHS >( ) ) ) )
            -> decltype( auto )
          requires (
              requires { SL_forward_like_app( std::declval< Lmb >( ) ); }
              && requires { SL_forward_like_app( std::declval< RHS >( ) ); } )
        {
          SL_forward_like_app( lhs );
          return SL_forward_like_app( rhs );
        } } )

#define SL_lambda_member_variadic_op( name )                                                           \
  template < class Lmb,                                                                                \
             details::satisfy< operator_with_lambda_enabled, operators_t< operators::name > >... RHS > \
  SL_using_m name( this Lmb&& lmb, RHS&&... rhs )                                                      \
      SL_expr_equiv( ::short_lambda::lambda{ details::demux( function_object::name,                    \
                                                             std::forward< Lmb >( lmb ),               \
                                                             std::forward< RHS >( rhs )... ) } );


    SL_lambda_member_variadic_op( function_call )
    SL_lambda_member_variadic_op( subscript )
#undef SL_lambda_member_variadic_op

#define SL_lambda_member_binary_op_named( name )                                                    \
  template < class Lmb,                                                                             \
             details::satisfy< operator_with_lambda_enabled, operators_t< operators::name > > RHS > \
  SL_using_m name( this Lmb&& lmb, RHS&& rhs )                                                      \
      SL_expr_equiv( ::short_lambda::lambda{ details::demux( function_object::name,                 \
                                                             std::forward< Lmb >( lmb ),            \
                                                             std::forward< RHS >( rhs ) ) } );

    SL_lambda_member_binary_op_named( assign_to ) // avoid overloading copy/move assign operator!
    SL_lambda_member_binary_op_named( pointer_member_access )

#undef SL_lambda_member_binary_op_named

#define SL_lambda_member_binary_op( name, op )                                                      \
  template < class Lmb,                                                                             \
             details::satisfy< operator_with_lambda_enabled, operators_t< operators::name > > RHS > \
  SL_using_m operator SL_remove_parenthesis( op )( this Lmb&& lmb, RHS&& rhs )                      \
      SL_expr_equiv( ::short_lambda::lambda{ details::demux( function_object::name,                 \
                                                             std::forward< Lmb >( lmb ),            \
                                                             std::forward< RHS >( rhs ) ) } );


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

#define SL_lambda_member_cast_op_named( name )                                                     \
  template < class Target, class Lmb >                                                             \
  SL_using_m name( this Lmb&& lmb, std::type_identity< Target > = { } )                            \
      SL_expr_equiv( ::short_lambda::lambda{ details::demux(                                       \
          details::bind_back( function_object::name, std::type_identity< Target >{ } ),            \
          std::forward< Lmb >( lmb ) ) } );

    SL_lambda_member_cast_op_named( const_cast_ )
    SL_lambda_member_cast_op_named( static_cast_ )
    SL_lambda_member_cast_op_named( dynamic_cast_ )
    SL_lambda_member_cast_op_named( reinterpret_cast_ )
    SL_lambda_member_cast_op_named( cstyle_cast )

#undef SL_lambda_member_cast_op_named

#define SL_lambda_member_unary_op_named( name )                                                    \
  template < class Lmb >                                                                           \
  SL_using_m name( this Lmb&& lmb ) SL_expr_equiv( ::short_lambda::lambda{                         \
      details::demux( function_object::name, std::forward< Lmb >( lmb ) ) } );

    SL_lambda_member_unary_op_named( throw_ )
    SL_lambda_member_unary_op_named( typeid_ )
    SL_lambda_member_unary_op_named( sizeof_ )
    SL_lambda_member_unary_op_named( alignof_ )
    SL_lambda_member_unary_op_named( typeof_ )
    SL_lambda_member_unary_op_named( typeof_unqual_ )
    SL_lambda_member_unary_op_named( co_await_ )

#undef SL_lambda_member_unary_op_named

    template < bool Id = false, class Lmb >
    SL_using_m decltype_( this Lmb&& lmb ) SL_expr_equiv( ::short_lambda::lambda{ details::demux(
        details::bind_back( function_object::decltype_, std::bool_constant< Id >{ } ),
        std::forward< Lmb >( lmb ) ) } );

    template < class Lmb >
    SL_using_m noexcept_( this Lmb&& lmb ) SL_expr_equiv( ::short_lambda::lambda {
      [lmb{ std::forward< Lmb >(
          lmb ) }]< class Self, class... Ts >( [[maybe_unused]] this Self&& self, Ts&&... args )
          SL_expr_equiv_declval( ( noexcept( SL_forward_like_app( std::declval< Lmb >( ) ) ) ),
                                 noexcept( SL_forward_like_app( lmb ) ) )
    } );

#define SL_lambda_membedr_unary_op( name, op )                                                     \
  template < class Lmb >                                                                           \
  SL_using_m operator SL_remove_parenthesis( op )( this Lmb&& lmb )                                \
      SL_expr_equiv( ::short_lambda::lambda{                                                       \
          details::demux( function_object::name, std::forward< Lmb >( lmb ) ) } );

    /// @note: msvc crashed with overloading operator& globally, so we overload it as member
    /// function
    SL_lambda_membedr_unary_op( address_of, (&) );
    SL_lambda_membedr_unary_op( indirection, (*) );
    SL_lambda_membedr_unary_op( object_member_access_of_pointer, (->) );

#undef SL_lambda_membedr_unary_op

    template < class Lmb >
    SL_using_m operator++( this Lmb&& lmb ) SL_expr_equiv( ::short_lambda::lambda{
        details::demux( function_object::pre_increment, std::forward< Lmb >( lmb ) ) } );
    template < class Lmb >
    SL_using_m operator++( this Lmb&& lmb, int ) SL_expr_equiv( ::short_lambda::lambda{
        details::demux( function_object::post_increment, std::forward< Lmb >( lmb ) ) } );
    template < class Lmb >
    SL_using_m operator--( this Lmb&& lmb ) SL_expr_equiv( ::short_lambda::lambda{
        details::demux( function_object::pre_decrement, std::forward< Lmb >( lmb ) ) } );
    template < class Lmb >
    SL_using_m operator--( this Lmb&& lmb, int ) SL_expr_equiv( ::short_lambda::lambda{
        details::demux( function_object::post_decrement, std::forward< Lmb >( lmb ) ) } );

    template <
        class Lmb,
        details::satisfy< operator_with_lambda_enabled, operators_t< operators::conditional > > TB,
        details::satisfy< operator_with_lambda_enabled, operators_t< operators::conditional > > FB >
    SL_using_m conditional( this Lmb&& lmb, TB&& tb, FB&& fb )
        SL_expr_equiv( ::short_lambda::lambda{ details::demux( function_object::conditional,
                                                               std::forward< Lmb >( lmb ),
                                                               std::forward< TB >( tb ),
                                                               std::forward< FB >( fb ) ) } );

    /// @note: for multiple lambda arguments, we only consider the friend new_ template of the first
    /// one.
    template < class T,
               details::satisfy< operator_with_lambda_enabled, operators_t< operators::new_ > >... Args >
      requires (
          details::first_satisfy< details::lpartial< details::is_same, self_t >::template type,
                                  std::remove_cvref_t< Args >... > )
    SL_using_f
    new_( std::type_identity< T >, Args&&... args1 ) SL_expr_equiv( ::short_lambda::lambda{
        details::demux( details::bind_front( function_object::new_, std::type_identity< T >{ } ),
                        std::forward< Args >( args1 )... ) } )

    template < bool Array = false, class Lmb >
    SL_using_m delete_( this Lmb&& lmb, std::bool_constant< Array > = { } )
        SL_expr_equiv( ::short_lambda::lambda{ details::demux(
            details::bind_back( function_object::delete_, std::bool_constant< Array >{ } ),
            std::forward< Lmb >( lmb ) ) } )
  };


  inline namespace factory_object {


    SL_using_v $0 = lambda{ factory::projector_t< 0 >{} };
    SL_using_v $1 = lambda{ factory::projector_t< 1 >{} };
    SL_using_v $2 = lambda{ factory::projector_t< 2 >{} };
    SL_using_v $3 = lambda{ factory::projector_t< 3 >{} };
    SL_using_v $4 = lambda{ factory::projector_t< 4 >{} };
    SL_using_v $5 = lambda{ factory::projector_t< 5 >{} };
    SL_using_v $6 = lambda{ factory::projector_t< 6 >{} };
    SL_using_v $7 = lambda{ factory::projector_t< 7 >{} };
    SL_using_v $8 = lambda{ factory::projector_t< 8 >{} };
    SL_using_v $9 = lambda{ factory::projector_t< 9 >{} };
    SL_using_v $  = factory::lift_t< /*Target*/ ::short_lambda::lambda >{ };

    template < class U, details::size_t id = 0 >
    SL_using_v $_
        = factory::coprojector_t< /*Target*/ ::short_lambda::lambda, U >{ }( storage< U, id > );

    template < auto value, details::size_t id = 0 >
    SL_using_v $c = factory::coprojector_t< /*Target*/ ::short_lambda::lambda,
                                            std::remove_reference_t< decltype( value ) > >{ }(
        factory::constant< value, id > );

  } // namespace factory_object

  inline namespace hkt {
    template < template < class > class > struct fmap_t; // Functor
    template < template < class > class > struct pure_t; // Applicative
    template < template < class > class > struct bind_t; // Monad

    template <>
    struct fmap_t< lambda > { // fmap<lambda> :: (a ... -> b) -> lambda<a> ... -> lambda<b>
      /// @note: This operator() need to be specially handled since if we just copy and paste the
      ///        lambda body (replace captures by `declval<>()`) it will trigger ICE of both clang
      ///        and gcc. Possibly due to we try to do some complicate lambda capture in a recursive
      ///        context.
      template < class Func >
      SL_using_paren( Func&& func ) SL_expr_equiv_declval(
          ( SL_decay_copy( std::forward< Func >( func ) ) ), // only handle copy/move construct
                                                             // capture here, lambda body is not in
                                                             // immediate context and since it's a
                                                             // dependent lambda, it's safe to delay
                                                             // checks
          [func{ std::forward< Func >(
              func ) }]< class Self, details::satisfy< is_short_lambda >... Ts >(
              [[maybe_unused]] this Self& self0,
              [[maybe_unused]] Ts&&... args0 )
              SL_expr_equiv_declval(
                  ( (void) SL_decay_copy(
                        details::forward_like< Self >( std::declval< Func&& >( ) ) ),
                    ( (void) SL_decay_copy( std::declval< Ts&& >( ) ), ... ) ), // again, we only
                                                                                // check decay copy
                                                                                // here.
                  ::short_lambda::lambda {
                    [
                      func{ details::forward_like< Self >( func ) },
                      ... args0{ std::forward< Ts >( args0 ) }
                    ]< class Self1, class... Ts1 >( [[maybe_unused]] this Self1&& self1,
                                                    Ts1&&... args1 )
                        SL_expr_equiv_declval(
                            ( details::forward_like< Self1 >(
                                details::forward_like< Self >( std::declval< Func&& >( ) ) )(
                                details::forward_like< Self1 >(
                                    std::forward< Ts >( std::declval< Ts&& >( ) ) )(
                                    std::forward< Ts1 >( std::declval< Ts1&& >( ) )... )... ) ),
                            details::forward_like< Self1 >( func )( details::forward_like< Self1 >(
                                args0 )( std::forward< Ts1 >( args1 )... )... ) )
                  } ) )
    };
    template <> struct pure_t< lambda >: factory::lift_t< lambda > { };
    template <> struct bind_t< lambda > {
      // bind<lambda> :: lambda<a>... -> (a... -> lambda<b>) -> lambda<b>
      template < details::satisfy< is_short_lambda >... Ts1 >
      SL_using_paren( Ts1&&... as ) // lambda<a>...
          SL_expr_equiv_spec( ( (void) SL_decay_copy( std::declval< Ts1&& >( ) ), ... ) ) {
        return // f :: a... -> lambda<b>
            [... as{ std::forward< Ts1 >(
                as ) } ]< class Self, class Func >( [[maybe_unused]] this Self&& self, Func&& func )
                SL_expr_equiv_spec( (void) SL_decay_copy(
                                        details::forward_like< Self >( std::declval< Func >( ) ) ),
                                    ( (void) SL_decay_copy( details::forward_like< Self >(
                                          std::declval< Ts1&& >( ) ) ),
                                      ... ) ) {
                  return lambda {
                    [
                      func{ details::forward_like< Self >( func ) },
                      ... as{ details::forward_like< Self >( as ) }
                    ]< class Self1, class... Ts >
                      requires ( details::satisfy<
                                 decltype( details::forward_like< Self1 >(
                                     details::forward_like< Self >( std::declval< Func && >( ) ) )(
                                     details::forward_like< Self1 >( std::declval< Ts1 && >( ) )(
                                         std::forward< Ts >( std::declval< Ts && >( ) )... )... ) ),
                                 is_short_lambda > ) // ensure that f(a(...)...) is lambda<b>
                    ( [[maybe_unused]] this Self1&& self1, Ts&&... args ) SL_expr_equiv(
                        details::forward_like< Self1 >( func )( details::forward_like< Self1 >( as )(
                            std::forward< Ts >( args )... )... )( std::forward< Ts >( args )... ) )
                  };
                };
      }
    };

    template < template < class > class Func > SL_using_v fmap = fmap_t< Func >{ };
    template < template < class > class Func > SL_using_v pure = pure_t< Func >{ };
    template < template < class > class Func > SL_using_v bind = bind_t< Func >{ };
  }; // namespace hkt

} // namespace short_lambda
