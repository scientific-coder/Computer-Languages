#include <iostream>
#include <sstream>
#include <vector>

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
#include <boost/mpl/plus.hpp>
#include <boost/mpl/size_t.hpp>
#include <boost/mpl/not.hpp>


#include "generic_union.hxx"
#include "apply.hxx"
#include <memory>

//g++-snapshot -std=c++0x conditional-jump.cxx   -o conditional-jump -Wall -O4 -march=native

/*
  Toy interpreter with double and int primitive type and an object type stored by pointer (as in Java).
  the program is a collection of variant<> that can be either opcode of immediate data (doubles or ptrs)
  it is then stored in more instructions that are untagged unions of of code or (bytes of for compact instructions) data.
  it is then executed in the loop.

  now using compound assignment operators when possible

  ->  load_i 1
  sub
  jump_if_true -XXX

TODO : add flyweight<std::string> for var ids
add labels to listing, and jump to labels
*/

constexpr bool  trace {false}; // I don't want to pollute each and every class & function with a bool template arg

constexpr bool test_assign_ops{true};

struct object;

//typedef std::shared_ptr<object> object_ptr; // TODO

typedef object* object_ptr;

typedef boost::mpl::vector<double, int> primitive_types;
typedef boost::mpl::push_front<primitive_types, object_ptr>::type types;

typedef boost::make_variant_over<types>::type var_type;

template<typename T1, typename T2>//only used for primitive types
struct arithmetic_promotion : boost::mpl::if_< boost::mpl::less< boost::mpl::distance< typename boost::mpl::find<primitive_types, T1>::type
                                                                                       ,typename boost::mpl::find<primitive_types, T2>::type >
                                                                 , boost::mpl::int_<0> >, T2, T1> {};

struct object {

  object(double v=1000.): value(v){}
  
  virtual void add(double v) {if(trace){std::cerr<<"adding "<< v <<" to an obj\n";} value += v;}
  virtual void add(int v) {if(trace){std::cerr<<"adding "<< v <<" to an obj\n";} value += v;}
  
  virtual void subtract(double v) {if(trace){std::cerr<<"subtracting "<< v <<" from an obj\n"; } value -=v;}
  virtual void subtract(int v) {if(trace){std::cerr<<"subtracting "<< v <<" from an obj\n"; } value -=v;}

  virtual var_type add_to(double v) {if(trace){std::cerr<<"adding an obj to"<< v <<"\n";} return v + value;}
  virtual var_type add_to(int v) {if(trace){std::cerr<<"adding an obj to"<< v <<"\n";} return v + value;}

  virtual var_type subtract_from(double v) {if(trace){std::cerr<<"subtracting an ob from"<< v <<"\n";} return v - value;}
  virtual var_type subtract_from(int v) {if(trace){std::cerr<<"subtracting an ob from"<< v <<"\n";} return v - value;}


  virtual void add(object_ptr o){if(trace){std::cerr<<"adding 2 obj\n";} value += o->value;}
  virtual void subtract(object_ptr o){if(trace){std::cerr<<"subtracting 2 obj\n"; } value -= o->value;}

  double value;
};

/* a binary op can use inplace operations iff:
  no object is invloved
  the result type is the same as the type of the first operand
 */
template<typename T1, typename T2> 
struct with_assign_op 
  : boost::mpl::and_< boost::mpl::bool_<test_assign_ops>
                      ,boost::mpl::and_< boost::mpl::not_<boost::mpl::or_< boost::is_same<T1, object_ptr>
                                                                           , boost::is_same<T2, object_ptr> > >
                                         ,boost::is_same<T1, typename arithmetic_promotion<T1, T2>::type > > > { };

template<typename Stack>
struct adder : boost::static_visitor<> {
  adder(Stack &s) : stack(s){}

  template<typename T1, typename T2> 
  typename boost::enable_if<with_assign_op<T1, T2>, void>::type operator()(T1& a1, T2 a2) { if(trace) { std::cerr<<"using compound assign op\n"; } a1+= a2; }

  template<typename T1, typename T2> 
  typename boost::disable_if<with_assign_op<T1, T2> , void>::type operator()(T1 a1, T2 a2)  { 
    typedef typename arithmetic_promotion<T1, T2>::type result_type;
    if(trace) { std::cerr<<"NOT using compound assign op\n"; }
    stack[stack.size()-2]= var_type(static_cast<result_type>(a1) + static_cast<result_type>(a2));
  }

  template<typename T1> 
  typename boost::disable_if<boost::is_same<T1, object_ptr>, void>::type operator()(T1 a1, object_ptr a2)  { stack[stack.size()-2]= a2->add_to(a1);  }

  template<typename T2> void operator()(object_ptr a1, T2 a2)  { a1->add(a2); }
  
   Stack& stack;
};

template<typename Stack>
struct subtracter :boost::static_visitor<void> {
  subtracter(Stack& s):stack(s){}

  template<typename T1, typename T2> 
  typename boost::enable_if<with_assign_op<T1, T2>, void>::type operator()(T1& a1, T2 a2) { if(trace) { std::cerr<<"using compound assign op\n"; } a1-= a2; }

  template<typename T1, typename T2> 
  typename boost::disable_if<with_assign_op<T1, T2> , void>::type operator()(T1 a1, T2 a2)  { 
    typedef typename arithmetic_promotion<T1, T2>::type result_type;
    if(trace) { std::cerr<<"NOT using compound assign op\n"; }
    stack[stack.size()-2]= var_type(static_cast<result_type>(a1) - static_cast<result_type>(a2));
  }

  template<typename T1> 
  typename boost::disable_if<boost::is_same<T1, object_ptr>, void>::type operator()(T1 a1, object_ptr a2) { stack[stack.size()-2]= a2->subtract_from(a1); }

  template<typename T2> void operator()(object_ptr a1, T2 a2) { a1->subtract(a2); }

  Stack& stack;
};

struct to_string :boost::static_visitor<std::string> {
  to_string(){}
  std::string operator()(double d) const { std::ostringstream out; out<<"double:"<<d<<'\n'; return out.str();}
  std::string operator()(int i) const { std::ostringstream out; out<<"int:"<<i<<'\n'; return out.str();}
  std::string operator()(object_ptr o) const { std::ostringstream out; out<<"object:"<<o<<'\n'; return out.str();}
};

struct to_bool :boost::static_visitor<bool> {
  to_bool(){}
  bool operator()(double d) const { return d != 0.;}
  bool operator()(int i) const { return i != 0;}
  bool operator()(object_ptr o) const { return o != 0;}
};


template <bool compact> struct make_opcode 
{ enum class type : typename boost::mpl::if_c<compact, char, int>::type { load_i, load_d, load_o, add, subtract, pop_one, jump_if_true, invalid, over}; };

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

template<typename...Types> struct total_sizeof ;
template<typename T> struct total_sizeof<T> : boost::mpl::long_<sizeof(T)> {};
template<typename First, typename...Rest> struct total_sizeof<First, Rest...> : boost::mpl::plus<total_sizeof<First>, total_sizeof<Rest...> > {};

template<typename Derived, typename instr_t> struct interpreter_base {
  typedef instr_t instruction_type;
  typedef typename instruction_type::opcode opcode;
  typedef std::vector<instruction_type> program_type;

  struct prog_loader : boost::static_visitor<> {
    prog_loader(program_type& prog):prog(prog), no_load(false){}
    void operator()(opcode op){ prog.emplace_back(op); 
      if(op == opcode::jump_if_true){ no_load = true; } // next int value in listing won't trigger a load instruction insertion
    }
    void operator()(double d){ prog.emplace_back(opcode::load_d); instruction_type::to_opcodes(d, std::back_inserter(prog)); }
    void operator()(int i){
      if(!no_load) {
        prog.emplace_back(opcode::load_i);
        no_load= false;
      }
      instruction_type::to_opcodes(i, std::back_inserter(prog)); 
    }
    void operator()(object* o){ prog.emplace_back(opcode::load_o); instruction_type::to_opcodes(o, std::back_inserter(prog)); }
    program_type& prog;
    bool no_load;
  };

  template<typename In> interpreter_base(In b, In e):a(stack), s(stack) {
    prog_loader loader(prog);
    std::for_each(b, e, boost::apply_visitor(loader));
  }

  template<typename...Args>
  std::vector<var_type> operator()(Args... a) { 
    std::vector<var_type> vars={a...};// contains args and then results
    {  // make code (prologue) to put args on the stack
      program_type prologue;// knowing the nb of args, we could reserve the size but meta prog is needed for compact opcodes
      prologue.reserve(sizeof...(Args) // load instructions (I trust the compiler to compute the expr it at compile time without using mpl)
                     +((sizeof(instruction_type)==1) ? total_sizeof<Args...>::value : sizeof...(Args))// inline values
                     +1);// over 
      prog_loader loader(prologue);
      std::for_each(vars.begin(), vars.end(), boost::apply_visitor(loader));
      vars.clear();
      prologue.emplace_back(opcode::over);
      // exec prologue
      static_cast<Derived&>(*this).exec(prologue.begin());
   }
  // jump to interpreter
    static_cast<Derived&>(*this).exec(prog.begin()); 
    stack.swap(vars); // clears stack and get results at the same time
    return vars;
  }

  program_type prog;
  typedef std::vector<var_type> stack_type;
  stack_type stack;
  adder<stack_type> a;
  subtracter<stack_type> s;
  to_string to_str;
  to_bool to_b;
};

template<bool stored_labels, typename instr_t> 
struct interpreter : interpreter_base<interpreter<stored_labels, instr_t>, instr_t > {
  typedef interpreter_base<interpreter<stored_labels, instr_t>, instr_t > base_type;
  typedef instr_t instruction_type;
  typedef typename instruction_type::opcode opcode;

  using base_type::stack ;
  using base_type::a ;
  using base_type::s ;
  using base_type::to_str ;
  using base_type::to_b ;
  using base_type::operator();
  //  using  interpreter_base<interpreter<stored_labels, instr_t>, instr_t >::interpreter_base<interpreter<stored_labels, instr_t>, instr_t >;
  template<typename In> interpreter(In b, In e): base_type(b, e){}
  template<typename In>
  var_type exec(In pc) {
    while(true){
      switch((*(pc++)).get_opcode()){
      case opcode::load_i: {
        stack.push_back(instruction_type::template read_data<int>(pc));
        if(trace){std::cerr<<"loading int:"<<boost::get<int>(stack.back())<<std::endl;}
        break;
      }
      case opcode::load_d: {
        stack.push_back(instruction_type::template read_data<double>(pc));
        if(trace){std::cerr<<"loading double:"<<boost::get<double>(stack.back())<<std::endl;}
        break;
      }
      case opcode::load_o: {
        stack.push_back(instruction_type::template read_data<object_ptr>(pc));
        if(trace){std::cerr<<"loading: object"<<boost::get<object_ptr>(stack.back())<<std::endl;}
        break;
      }
      case opcode::add: {
        var_type& tos1(*(&stack.back()-1));
        if(trace){ std::cerr<<"adding:\n"<< boost::apply_visitor(to_str, stack.back())<<  boost::apply_visitor(to_str, tos1)<<std::endl;}
        boost::apply_visitor(a, tos1, stack.back());
        stack.pop_back();
        if(trace){ std::cerr<<boost::apply_visitor(to_str, stack.back()) << std::endl;}
        break;
      }
      case opcode::subtract: {
        var_type& tos1(*(&stack.back()-1));
        if(trace){ std::cerr<<"subtracting:\n"<< boost::apply_visitor(to_str, stack.back())<< boost::apply_visitor(to_str, tos1)<<std::endl;}
        boost::apply_visitor(s, tos1, stack.back());
        stack.pop_back();
        if(trace){std::cerr<<boost::apply_visitor(to_str, stack.back())<<std::endl; }
        break;
      }
      case opcode::pop_one: {
        stack.pop_back();
        break;
      }
      case opcode::jump_if_true: {
        int delta(instruction_type::template read_data<int>(pc));
        if(boost::apply_visitor(to_b, stack.back())) { 
          if(trace) {
            std::cerr<<" jumping on true value\n";
            std::cerr<<"pc before jump:"<< (pc-base_type::prog.begin())<<std::endl;
          }
          if(trace) { std::cerr<<"pc after read jump:"<< (pc-base_type::prog.begin())<< " delta:"<<delta<<std::endl; }
          std::advance(pc, delta); 
        }
        if(trace) { std::cerr<<"pc after test:"<< (pc-base_type::prog.begin()) <<std::endl; }
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
    return stack.back();
  }
};

template<typename instr_t> // gcc specific fast dispatching using stored labels http://gcc.gnu.org/onlinedocs/gcc/Labels-as-Values.html
struct interpreter<true, instr_t> : interpreter_base<interpreter<true, instr_t>, instr_t> {
  typedef interpreter_base<interpreter<true, instr_t>, instr_t > base_type;
  typedef instr_t instruction_type;
  typedef typename instruction_type::opcode opcode;

  using base_type::stack ;
  using base_type::a ;
  using base_type::s ;
  using base_type::to_str ;
  using base_type::to_b ;
  using base_type::operator();
  //  using  interpreter_base<interpreter<true, instr_t>, instr_t >::interpreter_base<interpreter<true, instr_t>, instr_t >;
  template<typename In> interpreter(In b, In e): base_type(b, e){}

  template<typename In>
  var_type exec(In pc) {
    // it is a pity that I cannot have implicit int conversion when specifying the enum size :(
    static void* const instr[]={ &&load_i, &&load_d, &&load_o, &&add, &&subtract, &&pop_one, &&jump_if_true, &&invalid, &&over};
        #define DO_NOT_FACTOR // we can factor (or not) the common expressions of going to the next label and poping the stack when needed
#ifdef DO_NOT_FACTOR
  #define NEXT goto *instr[static_cast<int>((*pc++).get_opcode())]
  #define POP  stack.pop_back(); NEXT

#else
  #define NEXT goto next
  #define POP  goto with_pop
#endif
    NEXT;
#ifndef DO_NOT_FACTOR
  with_pop: stack.pop_back();
  next: goto *instr[static_cast<int>((*pc++).get_opcode())];
#endif

  load_i : {
      stack.push_back(instruction_type::template read_data<int>(pc));
      if(trace){std::cerr<<"loading int:"<<boost::get<int>(stack.back())<<std::endl;}
      NEXT;
    }
  load_d : {
      stack.push_back(instruction_type::template read_data<double>(pc));
      if(trace){std::cerr<<"loading double:"<<boost::get<double>(stack.back())<<std::endl;}
      NEXT;
    }
  load_o : {
      stack.push_back(instruction_type::template read_data<object_ptr>(pc));
      if(trace){std::cerr<<"loading object:"<<boost::get<object_ptr>(stack.back())<<std::endl;}
      NEXT;
    }
  add : {
      var_type& tos1(*(&stack.back()-1));
      if(trace){ std::cerr<<"adding:\n"<< boost::apply_visitor(to_str, stack.back())<<  boost::apply_visitor(to_str, tos1)<<std::endl;}
      boost::apply_visitor(a, tos1, stack.back());
      if(trace){ std::cerr<<boost::apply_visitor(to_str, tos1) << std::endl;}
      POP;
    }
  subtract : {
      var_type& tos1(*(&stack.back()-1));
      if(trace){ std::cerr<<"subtracting:\n"<< boost::apply_visitor(to_str, stack.back())<< boost::apply_visitor(to_str, tos1)<<std::endl;}
      boost::apply_visitor(s, tos1, stack.back());
      if(trace){ std::cerr<<boost::apply_visitor(to_str, tos1) << std::endl;}
      POP;
    }
  pop_one : {
      POP;
    }

  jump_if_true: {// TODO
      int delta(instruction_type::template read_data<int>(pc)); 
       if(boost::apply_visitor(to_b, stack.back())) { 
          if(trace) {
            std::cerr<<" jumping on true value\n";
            std::cerr<<"pc before jump:"<< (pc-base_type::prog.begin())<<std::endl;
          }
 
          if(trace) { std::cerr<<"pc after read jump:"<< (pc-base_type::prog.begin())<< " delta:"<<delta<<std::endl; }
          std::advance(pc, delta); 
        }
        if(trace) { std::cerr<<"pc after test:"<< (pc-base_type::prog.begin()) <<std::endl; }
        NEXT;
    }
  invalid : std::cerr<<"invalid opcode\n";
  over:
    return stack.back();
#undef NEXT
  }

};

int main(int argc, char* argv[]){
  // faster is large opcodes and _especially_ with stored labels
  constexpr bool compact_opcode= false;
  constexpr bool with_stored_labels= true; // gcc extension

  typedef instruction<compact_opcode> instruction_type;
  typedef instruction_type::opcode opcode;
  std::cout<<"instruction size:"<<sizeof(instruction_type)<<" opcode_size:"<<sizeof(opcode)<<std::endl;
  std::vector<boost::variant< opcode, double, int, object*> > listing;
  // instructions are implied in the listing : no load_op_X
  listing.emplace_back((trace ? 2 : 1000));//@0
  listing.emplace_back(123.456);//@2
  listing.emplace_back(128.256);//@4
  //listing.emplace_back(128.256);
  listing.emplace_back(new object());//@6
  listing.emplace_back(2.5);//@8
  listing.emplace_back(-1);//@10
  listing.emplace_back(opcode::add);//@12 2.5 + (-1)
  listing.emplace_back(opcode::subtract);//@13 object -...
  listing.emplace_back(opcode::add);//@14 128.256+ ...
  listing.emplace_back(opcode::add);//@15 123.456+ ...
  listing.emplace_back(opcode::pop_one);//@16
  listing.emplace_back(1);//@17
  listing.emplace_back(opcode::subtract);//@19 index -1
  listing.emplace_back(opcode::jump_if_true);//@20
  listing.emplace_back(compact_opcode ? -57: -20);//@21 2-23 goto 2
  listing.emplace_back(opcode::over);//@23
  interpreter<with_stored_labels,  instruction_type> inter(listing.begin(), listing.end());
  for(std::size_t i(0); i != (trace ? 1 : 10000); ++i)
    { inter(8888, -789., .75); } 

  return 0;
}
