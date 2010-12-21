#ifndef GENERIC_UNION_HXX
#define GENERIC_UNION_HXX

template <typename... Types> union generic_union;
template<> union generic_union<> {};

template<typename First,typename ... Rest>
union generic_union<First,Rest...>{
  First first;
  generic_union<Rest...> rest;
};

template<typename T> struct is_not_in_the_union{};
//template<typename T, typename... Types> T& get(generic_union<Types...>& gu);
template<typename T> T& get(generic_union<>& gu){ return is_not_in_the_union<T>();}
template<typename T, typename First, typename... Rest >
typename boost::disable_if_c<boost::is_same<T, First>::value, T&>::type 
get(generic_union<First, Rest...>& gu) {return get<T>(gu.rest);}
template<typename First, typename... Rest> First& get(generic_union<First, Rest...>& gu) {return gu.first;}

template<typename T> T const& get(generic_union<> const& gu){ return is_not_in_the_union<T>();}
template<typename T, typename First, typename... Rest >
typename boost::disable_if_c<boost::is_same<T, First>::value, T const&>::type 
get(generic_union<First, Rest...> const& gu) {return get<T>(gu.rest);}
template<typename First, typename... Rest> First const& get(generic_union<First, Rest...> const& gu) {return gu.first;}


#endif
