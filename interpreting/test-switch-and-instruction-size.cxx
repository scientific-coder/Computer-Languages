#include <iostream>
#include <sstream>
#include <vector>
#include <stack>
#include <algorithm>
#include <functional>
#include <boost/variant/variant.hpp>
#include <boost/variant/apply_visitor.hpp>
#include <boost/variant/get.hpp>
#include <boost/mpl/vector.hpp>
#include <boost/mpl/find.hpp>
#include <boost/mpl/push_back.hpp>
#include <boost/mpl/push_front.hpp>
#include <boost/mpl/less.hpp>
#include <boost/mpl/int.hpp>
#include <boost/mpl/distance.hpp>
#include "generic_union.hxx"
#include "apply.hxx"
#include <memory>

//g++-snapshot -std=c++0x test-switch-and-instruction-size.cxx   -o test-switch-and-instruction-size -Wall -O4 -march=native

/*
  Toy interpreter with double and int primitive type and an object type stored by pointer (as in Java).
  the program is a collection of variant<> that can be either opcode of immediate data (doubles or ptrs)
  it is then stored in more instructions that are untagged unions of of code or (bytes of for compact instructions) data.
  it is then executed in the loop.
  ->  load_i 1
  sub
  jump_if_true -XXX
*/

constexpr bool  trace {false}; // I don't want to pollute each and every class & function with a bool template arg

struct object;

//typedef std::shared_ptr<object> object_ptr; // TODO

typedef object* object_ptr;

typedef boost::mpl::vector<double, int> primitive_types;
typedef boost::mpl::push_front<primitive_types, object_ptr>::type types;

typedef boost::make_variant_over<types>::type var_type;

template<typename T1, typename T2>//only used for primitive types
struct arithmetic_promotion : boost::mpl::if_< boost::mpl::less< boost::mpl::distance< typename boost::mpl::find<primitive_types, T1>::type
                                                                                       ,typename boost::mpl::find<primitive_types, T2>::type >
                                                                 , boost::mpl::int_<0> >, T1, T2> {};

struct object {
  virtual var_type add(double d) {if(trace){std::cerr<<"adding "<<d<<" to an obj\n";} return d+1000.;}
  virtual var_type subtract( double d) {if(trace){std::cerr<<"subtracting "<<d<<" from an obj\n"; }return 1000.-d;}

  virtual var_type add_to( double d) {if(trace){std::cerr<<"adding an obj to"<<d<<"\n";} return 1000.+d;}
  virtual var_type subtract_from( double d) {if(trace){std::cerr<<"subtracting an ob from"<<d<<"\n";} return d-1000.;}

  virtual var_type add(object_ptr o){if(trace){std::cerr<<"adding 2 obj\n";} return object_ptr(this);}
  virtual var_type subtract(object_ptr o){if(trace){std::cerr<<"subtracting 2 obj\n"; }return object_ptr(this);}

};

struct adder :boost::static_visitor<var_type> {
  adder(){}
  template<typename T1, typename T2> 
  typename boost::disable_if<boost::mpl::or_<boost::is_same<T1, object_ptr>, boost::is_same<T2, object_ptr> >
                             , var_type>::type 
                             operator()(T1 a1, T2 a2) const { 
    typedef typename arithmetic_promotion<T1, T2>::type result_type;
    return static_cast<result_type>(a1) + static_cast<result_type>(a2);
  }
template<typename T1> 
typename boost::disable_if<boost::is_same<T1, object_ptr>, var_type>::type 
operator()(T1 a1, object_ptr a2) const { return a2->add_to(a1); }
template<typename T2> 
var_type operator()(object_ptr a1, T2 a2) const { return a1->add(a2); }
};

struct subtracter :boost::static_visitor<var_type> {
  subtracter(){}
  template<typename T1, typename T2> 
  typename boost::disable_if<boost::mpl::or_<boost::is_same<T1, object_ptr>, boost::is_same<T2, object_ptr> >
                             , var_type>::type 
                             operator()(T1 a1, T2 a2) const { 
    typedef typename arithmetic_promotion<T1, T2>::type result_type;
    return static_cast<result_type>(a1) - static_cast<result_type>(a2);
  }
template<typename T1> 
typename boost::disable_if<boost::is_same<T1, object_ptr>, var_type>::type 
operator()(T1 a1, object_ptr a2) const { return a2->subtract_from(a1); }
template<typename T2> 
var_type operator()(object_ptr a1, T2 a2) const { return a1->subtract(a2); }
};

struct to_string :boost::static_visitor<std::string> {
  to_string(){}
  std::string operator()(double d) const { std::ostringstream out; out<<"double:"<<d<<'\n'; return out.str();}
  std::string operator()(int i) const { std::ostringstream out; out<<"int:"<<i<<'\n'; return out.str();}
  std::string operator()(object_ptr o) const { std::ostringstream out; out<<"object:"<<o<<'\n'; return out.str();}
};

template <bool compact> struct make_opcode {
  enum class type : typename boost::mpl::if_c<compact, char, int>::type { load_i, load_d, load_o, add, subtract, jump_if_true, invalid, over};
};

template<bool compact=true>
union instruction {
  typedef typename make_opcode<true>::type opcode;
  template<typename T>
  union as_bytes {
    as_bytes():data(){}
    T data;
    char bytes[sizeof(T)];
  };

  instruction(opcode op= opcode::invalid):op(op){}
  instruction(char byte):byte(byte){}

  template<typename T, typename Out> static Out to_opcodes( T d, Out o) 
  { as_bytes<T> b; b.data= d; return std::copy_n(b.bytes, sizeof(T), o); }


  template<typename T, typename In> static T read_data(In& i){
    as_bytes<T> b;
    std::transform(i, i+sizeof(T), b.bytes, [] (instruction i) {return i.byte;});//std::bind(&instr::byte, std::placeholders::_1)); or mem_fun(): ICE
    std::advance(i, sizeof(T));
    return b.data;
  }

  opcode get_opcode() const {return op;}

  char byte;
  opcode op;
};

template<>
union instruction<false> {
  typedef typename make_opcode<false>::type opcode;
  typedef apply<generic_union, boost::mpl::push_back<types, opcode >::type >::type union_type;

  instruction(opcode op= opcode::invalid){get<opcode>(data)=op;}

  template<typename T>  instruction(T d){get<T>(data)=d;}

  template<typename T, typename Out> static Out to_opcodes( T d, Out o) { *o=instruction<false>(d); return ++o; }

  template<typename T, typename In> static T read_data(In& i) { return get<T>((*(i++)).data); }

  opcode get_opcode() const {return get<opcode>(data);}

  union_type data;
};


template<typename Derived, typename instr_t> struct interpreter_base {
  typedef instr_t instruction_type;
  typedef typename instruction_type::opcode opcode;
  typedef std::vector<instruction_type> program_type;

  struct prog_loader : boost::static_visitor<> {
    prog_loader(program_type& prog):prog(prog){}
    void operator()(opcode op){ prog.emplace_back(op); }
    void operator()(double d){ prog.emplace_back(opcode::load_d); instruction_type::to_opcodes(d, std::back_inserter(prog)); }
    void operator()(int i){ prog.emplace_back(opcode::load_i); instruction_type::to_opcodes(i, std::back_inserter(prog)); }
    void operator()(object* o){ prog.emplace_back(opcode::load_o); instruction_type::to_opcodes(o, std::back_inserter(prog)); }
    program_type& prog;
  };

  template<typename In> interpreter_base(In b, In e){ 
    prog_loader loader(prog);
    std::for_each(b, e, boost::apply_visitor(loader));}

  void operator()() { 
    static_cast<Derived&>(*this)(prog.begin()); 
    while(!stack.empty()) {stack.pop();}
  }
  
  program_type prog;
  std::stack<var_type> stack;
  adder a;
  subtracter s;
  to_string to_str;
};

template<bool stored_labels, typename instr_t> struct interpreter : interpreter_base<interpreter<stored_labels, instr_t>, instr_t > {
  typedef interpreter_base<interpreter<stored_labels, instr_t>, instr_t > base_type;
  typedef instr_t instruction_type;
  typedef typename instruction_type::opcode opcode;

  using base_type::stack ;
  using base_type::a ;
  using base_type::s ;
  using base_type::to_str ;
  using base_type::operator();
  //  using  interpreter_base<interpreter<stored_labels, instr_t>, instr_t >::interpreter_base<interpreter<stored_labels, instr_t>, instr_t >;
  template<typename In> interpreter(In b, In e): base_type(b, e){}
  template<typename In>
  var_type operator()(In pc) {
    while(true){
      switch((*(pc++)).get_opcode()){
      case opcode::load_i: {
        stack.push(instruction_type::template read_data<int>(pc));
        if(trace){std::cerr<<"loading int:"<<boost::get<int>(stack.top())<<std::endl;}
        break;
      }
      case opcode::load_d: {
        stack.push(instruction_type::template read_data<double>(pc));
        if(trace){std::cerr<<"loading double:"<<boost::get<double>(stack.top())<<std::endl;}
        break;
      }
      case opcode::load_o: {
        stack.push(instruction_type::template read_data<object_ptr>(pc));
        if(trace){std::cerr<<"loading: object"<<boost::get<object_ptr>(stack.top())<<std::endl;}
        break;
      }
      case opcode::add: {
        var_type& tos1(*(&stack.top()-1));
        if(trace){ std::cerr<<"adding:\n"<< boost::apply_visitor(to_str, stack.top())<<  boost::apply_visitor(to_str, tos1)<<std::endl;}
        tos1= boost::apply_visitor(a, tos1, stack.top());
        stack.pop();
        if(trace){ std::cerr<<boost::apply_visitor(to_str, stack.top()) << std::endl;}
        break;
      }
      case opcode::subtract: {
        var_type& tos1(*(&stack.top()-1));
        if(trace){ std::cerr<<"subtracting:\n"<< boost::apply_visitor(to_str, stack.top())<< boost::apply_visitor(to_str, tos1)<<std::endl;}
        tos1=boost::apply_visitor(s, tos1, stack.top());
        stack.pop();
        boost::apply_visitor(to_str, stack.top());
        break;
      }
      case opcode::jump_if_true: {
        //TODO
        break;
      }
      case opcode::invalid: {
        std::cerr<<"invalid opcode\n";
      } // no break
      case opcode::over: {
        goto over;
      }
      }
      if(trace){ std::cerr<<"stack.size()="<<stack.size()<<std::endl; }
    }
  over:
    return stack.top();
  }
};

template<typename instr_t> struct interpreter<true, instr_t> : interpreter_base<interpreter<true, instr_t>, instr_t> {
  typedef interpreter_base<interpreter<true, instr_t>, instr_t > base_type;
  typedef instr_t instruction_type;
  typedef typename instruction_type::opcode opcode;

  using base_type::stack ;
  using base_type::a ;
  using base_type::s ;
  using base_type::to_str ;
  using base_type::operator();
  //  using  interpreter_base<interpreter<true, instr_t>, instr_t >::interpreter_base<interpreter<true, instr_t>, instr_t >;
  template<typename In> interpreter(In b, In e): base_type(b, e){}

  template<typename In>
  var_type operator()(In pc) {
    // it is a pity that I cannot have implicit int conversion when specifying the enum size :(
    static void* instr[]={ &&load_i, &&load_d, &&load_o, &&add, &&subtract, &&jump_if_true, &&invalid, &&over};
    //#define DO_NOT_FACTOR
#ifdef DO_NOT_FACTOR
    goto *instr[static_cast<int>((*pc++).get_opcode())];
  load_i : {
      stack.push(instruction_type::template read_data<int>(pc));
      if(trace){std::cerr<<"loading int:"<<boost::get<int>(stack.top())<<std::endl;}
      goto *instr[static_cast<int>((*pc++).get_opcode())];
    }
  load_d : {
      stack.push(instruction_type::template read_data<double>(pc));
      if(trace){std::cerr<<"loading double:"<<boost::get<double>(stack.top())<<std::endl;}
      goto *instr[static_cast<int>((*pc++).get_opcode())];
    }
  load_o : {
      stack.push(instruction_type::template read_data<object_ptr>(pc));
      if(trace){std::cerr<<"loading object:"<<boost::get<object_ptr>(stack.top())<<std::endl;}
      goto *instr[static_cast<int>((*pc++).get_opcode())];
    }
  add : {
      var_type& tos1(*(&stack.top()-1));
      if(trace){ std::cerr<<"adding:\n"<< boost::apply_visitor(to_str, stack.top())<<  boost::apply_visitor(to_str, tos1)<<std::endl;}
      tos1= boost::apply_visitor(a, tos1, stack.top());
      stack.pop();
      if(trace){ std::cerr<<boost::apply_visitor(to_str, stack.top()) << std::endl;}
      goto *instr[static_cast<int>((*pc++).get_opcode())];
    }
  subtract : {
      var_type& tos1(*(&stack.top()-1));
      if(trace){ std::cerr<<"subtracting:\n"<< boost::apply_visitor(to_str, stack.top())<< boost::apply_visitor(to_str, tos1)<<std::endl;}
      tos1=boost::apply_visitor(s, tos1, stack.top());
      stack.pop();
      if(trace){ std::cerr<<boost::apply_visitor(to_str, stack.top()) << std::endl;}
      goto *instr[static_cast<int>((*pc++).get_opcode())];
    }
  jump_if_true: {// TODO
      goto *instr[static_cast<int>((*pc++).get_opcode())];
    }
  invalid : std::cerr<<"invalid opcode\n";
  over:
#else
    goto next;
  with_pop: stack.pop();
  next: goto *instr[static_cast<int>((*pc++).get_opcode())];
  load_i : {
      stack.push(instruction_type::template read_data<int>(pc));
      if(trace){std::cerr<<"loading int:"<<boost::get<int>(stack.top())<<std::endl;}
      goto next;
    }
  load_d : {
      stack.push(instruction_type::template read_data<double>(pc));
      if(trace){std::cerr<<"loading double:"<<boost::get<double>(stack.top())<<std::endl;}
      goto next;
    }
  load_o : {
      stack.push(instruction_type::template read_data<object_ptr>(pc));
      if(trace){std::cerr<<"loading object:"<<boost::get<object_ptr>(stack.top())<<std::endl;}
      goto next;
    }
  add : {
      var_type& tos1(*(&stack.top()-1));
      if(trace){ std::cerr<<"adding:\n"<< boost::apply_visitor(to_str, stack.top())<<  boost::apply_visitor(to_str, tos1)<<std::endl;}
      tos1= boost::apply_visitor(a, tos1, stack.top());
      if(trace){ std::cerr<<boost::apply_visitor(to_str, tos1) << std::endl;}
      goto with_pop;
    }
  subtract : {
      var_type& tos1(*(&stack.top()-1));
      if(trace){ std::cerr<<"subtracting:\n"<< boost::apply_visitor(to_str, stack.top())<< boost::apply_visitor(to_str, tos1)<<std::endl;}
      tos1=boost::apply_visitor(s, tos1, stack.top());
      if(trace){ std::cerr<<boost::apply_visitor(to_str, tos1) << std::endl;}
      goto with_pop;
    }
  jump_if_true: {// TODO
      goto next;
    }
  invalid : std::cerr<<"invalid opcode\n";
  over:
#endif
    return stack.top();
  }

};

int main(int argc, char* argv[]){
  // faster is large opcodes and _especially_ with stored labels
  constexpr bool compact_opcode= false;
  constexpr bool with_stored_labels= false; // gcc extension

  typedef instruction<compact_opcode> instruction_type;
  typedef instruction_type::opcode opcode;
  std::cout<<"instruction size:"<<sizeof(instruction_type)<<" opcode_size:"<<sizeof(opcode)<<std::endl;
  std::vector<boost::variant< opcode, double, object*> > listing;
  listing.emplace_back(555.666);
  for( std::size_t i(0); i != (trace ? 1 : 100); ++i) {
    listing.emplace_back(123.456);
    listing.emplace_back(128.256);
    listing.emplace_back(new object());
    listing.emplace_back(-1.);
    listing.emplace_back(opcode::add);
    listing.emplace_back(opcode::subtract);
    listing.emplace_back(opcode::add);
    listing.emplace_back(opcode::add);
  }
  listing.emplace_back(opcode::over);
  interpreter<with_stored_labels,  instruction_type> inter(listing.begin(), listing.end());
  for(std::size_t i(0); i != (trace ? 1 : 10000); ++i)
    { inter(); } 

  return 0;
}
