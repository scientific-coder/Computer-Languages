// (C) Bernard Hugueney, licence GPL v3
#include <string>
#include <iostream>

#include <boost/lexical_cast.hpp>

#include <boost/spirit/include/qi.hpp>
#include <boost/spirit/include/phoenix_operator.hpp>
#include <boost/spirit/include/phoenix_function.hpp>

#include <llvm/LLVMContext.h>
#include <llvm/Module.h>
#include <llvm/Function.h>
#include <llvm/PassManager.h>
#include <llvm/Analysis/Verifier.h>
#include <llvm/Assembly/PrintModulePass.h>
#include <llvm/Support/IRBuilder.h>
#include <llvm/Support/raw_ostream.h>
#include <llvm/DerivedTypes.h>
#include <llvm/ExecutionEngine/ExecutionEngine.h>
#include <llvm/Target/TargetData.h>
#include <llvm/Target/TargetSelect.h>
#include <llvm/Transforms/Scalar.h>
#include <llvm/ExecutionEngine/JIT.h>
// see http://lists.cs.uiuc.edu/pipermail/llvm-commits/Week-of-Mon-20101115/112020.html
#include <llvm/Support/NoFolder.h>

using namespace llvm;


// g++ -o lang_1-llvm lang_1-llvm.cxx `llvm-config-2.8 --cppflags --ldflags --libs ` -lstdc++ -rdynamic

using namespace boost::spirit;
using namespace boost::spirit::qi;
using namespace boost::spirit::ascii;



template<typename T> static const Type* type(){ return "unkown type!";}// error
template<> const Type* type<void>()  { return Type::getVoidTy(getGlobalContext());}
template<> const Type* type<int>()   { return Type::getInt32Ty(getGlobalContext());}
template<> const Type* type<long>()  { return Type::getInt64Ty(getGlobalContext());}
template<> const Type* type<float>() { return Type::getFloatTy(getGlobalContext());}
template<> const Type* type<double>(){ return Type::getDoubleTy(getGlobalContext());}


template<typename T> struct numeric_parser{};

template<>  struct numeric_parser<short>{
  typedef const short__type type;
  static type parser;
};
numeric_parser<short>::type numeric_parser<short>::parser=short_;

template<> struct   numeric_parser<int>{
  typedef const int__type type;
  static type parser;
};
numeric_parser<int>::type numeric_parser<int>::parser=int_;

template<>  struct  numeric_parser<long>{
  typedef const long__type type;
  static type parser;
};
numeric_parser<long>::type numeric_parser<long>::parser=long_;

template<>  struct  numeric_parser<float>{
  typedef const float__type type;
  static type parser;
};
numeric_parser<float>::type numeric_parser<float>::parser=float_;

template<>  struct  numeric_parser<double>{
  typedef const double__type type;
  static type parser;
};

numeric_parser<double>::type numeric_parser<double>::parser=double_;

template<>  struct  numeric_parser<long double>{
  typedef const long_double_type type;
  static type parser;
};

numeric_parser<long double>::type numeric_parser<long double>::parser=long_double;

// arithmetic expression grammar, using actions to insert nodes into the AST
template <typename value_t, typename Iterator, typename Builder>
struct language_1_grammar : grammar<Iterator, Module*(), boost::spirit::standard::space_type> {

 struct builder_helper{
   template<typename T1, typename T2=T1, typename T3=T2, typename T4=T3> struct result{ typedef Value* type;};
   builder_helper(Builder& b):builder(b){}
   typedef Value* (Builder::*binary_op_t)(Value*, Value*, const Twine&);
   typedef Value* (Builder::*unary_op_t)(Value*, const Twine&);
   typedef ReturnInst* (Builder::*op_no_name )(Value*);

   Value* operator()(binary_op_t op, Value* a1, Value* a2, const char * name) const
   { return (builder.*op)(a1, a2, name); }
   Value* operator()(unary_op_t op, Value* a, const char * name) const
   { return (builder.*op)(a, name); }
   Value* operator()(op_no_name op, Value* const& a) const
   { return (builder.*op)(a); }
   Value* operator()(short v) const { return ConstantInt::get(getGlobalContext(), APInt(sizeof(short)*8, v)); }
   Value* operator()(int v)   const { return ConstantInt::get(getGlobalContext(), APInt(sizeof(int)*8, v)); }
   Value* operator()(long v)  const { return ConstantInt::get(getGlobalContext(), APInt(sizeof(long)*8, v)); }
   Value* operator()(float v) const { return ConstantFP::get(getGlobalContext(), APFloat(v)); }
   Value* operator()(double v)const{ return ConstantFP::get(getGlobalContext(), APFloat(v)); }

   Builder& builder;
 };

  language_1_grammar(char const * const name) 
  : language_1_grammar::base_type(module),
    module_ptr(new Module(name, getGlobalContext()))
  , build(*(new Builder(BasicBlock::Create(getGlobalContext(),"entry",
					       cast<Function>(module_ptr->getOrInsertFunction("main", type<value_t>(), NULL))))))
    
{
  module = program[_val=module_ptr];

  program = additive_expression [_val=build(&Builder::CreateRet,_1)]
    ;

  additive_expression =
    multiplicative_expression               [_val=_1]
       >> *(
	 ('+' >> multiplicative_expression  
	  [_val= build(&Builder::CreateAdd, _val, _1,"addtmp")])
	 |('-' >> multiplicative_expression 
	   [_val=build(&Builder::CreateSub, _val, _1,"subtmp")])
				      )
    ;
    multiplicative_expression =
      factor               [_val=_1]
       >> *(
	   ('*' >> factor[_val= build(&Builder::CreateMul, _val, _1, "multmp")])
	   |('/' >> factor [_val = build(&Builder::CreateSDiv, _val, _1, "divtmp")])
	   )
      ;

    factor =
      numeric_to_val             [_val=_1]
      | '(' >> additive_expression  [_val=_1] >> ')'
      |   ('-' >> factor
	   [_val= build(&Builder::CreateNeg, _1,"negtmp")]
	   )
      |   ('+' >> factor          [_val=_1])
      ;
    numeric_to_val = numeric_parser<value_t>::parser[_val=build(_1)];
 }
    rule<Iterator, Value*(), boost::spirit::standard::space_type> additive_expression, multiplicative_expression
      , factor, numeric_to_val, program;
    rule<Iterator, Module*(), boost::spirit::standard::space_type> module;

    Module* module_ptr;
    boost::phoenix::function<builder_helper> build;
};

int main(int argc, char* argv[]){
  typedef int value_t; // value used in arithmetic computations

  if(argc > 2 )
    { std::cerr<< "Usage: "<<argv[0]<<" [nb of executions]\n"; return 1;}

  std::cin.unsetf(std::ios::skipws); //  Turn off white space skipping on the stream

  typedef std::string buffer_t;
  buffer_t buffer(std::istream_iterator<char>(std::cin), (std::istream_iterator<char>()));
  typedef buffer_t::const_iterator iter_t;
  iter_t iter(buffer.begin()), end(buffer.end());

  typedef language_1_grammar<value_t, iter_t, llvm::IRBuilder<true, NoFolder> > grammar_t;
  Module* module_ptr(0);
  grammar_t grammar("lang_1");
  bool r = phrase_parse(iter, end, grammar, boost::spirit::standard::space, module_ptr);

  if (r && iter == end) {
    std::cout<<"parsing succeded !\n";
    verifyModule(*module_ptr, PrintMessageAction);
    module_ptr->dump();
    llvm::InitializeNativeTarget();
    std::string ErrStr;
    llvm::ExecutionEngine* exec_engine_ptr= llvm::EngineBuilder(module_ptr).setErrorStr(&ErrStr).create();
  if (!exec_engine_ptr) {
    std::cerr<<"Could not create ExecutionEngine:"<< ErrStr.c_str()<<std::endl;
  }else {
    typedef value_t (*fun_ptr_t)(void);
    fun_ptr_t fun_ptr = 
      reinterpret_cast<fun_ptr_t>(exec_engine_ptr->getPointerToFunction(module_ptr->getFunction("main")));
    std::cout<<"result: "<<(*fun_ptr)()<<std::endl;
  }
  } else {
    std::string rest(iter, end);
    std::cerr << "parsing failed\n" << "stopped at: \"" << rest << "\"\n";
  }
  delete module_ptr;
  return r ? 0 : 1 ;
}
