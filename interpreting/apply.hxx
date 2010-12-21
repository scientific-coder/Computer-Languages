#ifndef APPLY_HXX
#include <boost/mpl/empty.hpp>
#include <boost/mpl/pop_back.hpp>
#include <boost/mpl/back.hpp>

template<template<typename...> class T, bool empty, typename C, typename... Types> struct apply_helper {
  typedef typename boost::mpl::pop_back<C>::type rest;
  typedef typename apply_helper<T, boost::mpl::empty<rest>::value, rest, typename boost::mpl::back<C>::type, Types...>::type type;
};
template<template<typename...> class T,typename C, typename... Types> struct apply_helper<T, true, C, Types...> {
  typedef T<Types...> type;
};

template<template<typename...> class T,typename C> struct apply : apply_helper<T, boost::mpl::empty<C>::value, C> {};
#endif
