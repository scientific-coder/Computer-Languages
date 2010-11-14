// (C) Bernard Hugueney, licence GPL v3
#include <string>
#include <iostream>

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

//#include "IRBuilderNoFold.h" // 

using namespace llvm;

/*
lang_2 : variables declarations and assignments with infix arithmetic expressions, ends with a return statement.

Default llvm Internal Representation Builder does constant folding.

Variables mapping name->adress is handled directly by spirit::symbols<>

Much of the code is there only to enable support for all numeric types (short, int, long, float, double) as valid value_t.

TODO: handle llvm numeric op dispatch to fp type (change since 2.6)
 */

// time g++ -o lang_2-llvm lang_2-llvm.cxx `llvm-config-2.8 --cppflags --ldflags --libs ` -lstdc++ -rdynamic -O4

using namespace boost::spirit;
using namespace boost::spirit::qi;
using namespace boost::spirit::standard;


// template function to map  C++ type -> llvm::Type
template<typename T> static const Type* type(){ return "unkown type!";}// error
template<> const Type* type<void>()  { return Type::getVoidTy(getGlobalContext());}
template<> const Type* type<int>()   { return Type::getInt32Ty(getGlobalContext());}
template<> const Type* type<long>()  { return Type::getInt64Ty(getGlobalContext());}
template<> const Type* type<float>() { return Type::getFloatTy(getGlobalContext());}
template<> const Type* type<double>(){ return Type::getDoubleTy(getGlobalContext());}

// template structs to map C++ type -> Spirit2 numeric parser
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


// now the real deal, at last ! :-)
// arithmetic expression grammar, using semantic actions to create llvm internal representation
template <typename value_t, typename Iterator>
struct language_2_grammar : grammar<Iterator, space_type> {

  // symbols map use to store varables names and map them to the relevant llvm node
  typedef symbols<char,AllocaInst*> vars_t;

  // functor strucuture used to create llvm internal representation
  // (ab)using a lot boost::phoenix::function<> ability to overload operator() !
  struct builder_helper{
    // typedef to ease to use of pointers to member function
    typedef Value* (IRBuilder<>::*binary_op_t)(Value*, Value*, const Twine&);
    typedef Value* (IRBuilder<>::*unary_op_t)(Value*, const Twine&);
    // template structs to have different result type according to the argument types
  // template structs to have different result type according to the argument types
    //def -> Value*
    //(AllocaInst*, Value*) ->StoreInst*
    //(std::string const) -> AllocaInst*
    //(Value*) -> ReturnInst*
    template<typename T1, typename T2=void, typename T3=void, typename T4=void> 
  struct result : boost::mpl::if_<
    boost::mpl::and_<boost::is_same<T1, AllocaInst*>
		     ,boost::is_same<T2, Value*> >
		       , StoreInst* 
		       , typename boost::mpl::if_<boost::is_same<T1, std::string>
					 , AllocaInst*
					 , typename boost::mpl::if_<boost::is_same<T1, Value*>
							   , ReturnInst*
							   , Value*>::type >::type > {};

    builder_helper(vars_t &v, IRBuilder<>& b):vars(v), builder(b){}
    
    // binary operations
    Value* operator()(binary_op_t op, Value* a1, Value* a2, const char * name) const
    { return (builder.*op)(a1, a2, name); }
    // unary operation
    Value* operator()(unary_op_t op, Value* a, const char * name) const
    { return (builder.*op)(a, name); }
    // return instruction
    ReturnInst* operator()(Value*  a) const { return builder.CreateRet(a); }
    // variable assignment
    StoreInst* operator()(AllocaInst* variable, Value* value ) const
    { return builder.CreateStore(value, variable, false); }
    // reading a variable value
    Value* operator()(AllocaInst* variable) const {return builder.CreateLoad(variable);}
    // variable declaration
    AllocaInst* operator()(std::string const& name) const{
      AllocaInst* res(builder.CreateAlloca(type<value_t>(),0, name.c_str()));
      vars.add(name.begin(), name.end(), res);
      return res;
    }
    // constant values
    Value* operator()(short v) const { return ConstantInt::get(getGlobalContext(), APInt(sizeof(short)*8, v)); }
    Value* operator()(int v)   const { return ConstantInt::get(getGlobalContext(), APInt(sizeof(int)*8, v)); }
    Value* operator()(long v)  const { return ConstantInt::get(getGlobalContext(), APInt(sizeof(long)*8, v)); }
    Value* operator()(float v) const { return ConstantFP::get(getGlobalContext(), APFloat(v)); }// APFloat()
    Value* operator()(double v)const { return ConstantFP::get(getGlobalContext(), APFloat(v)); }// is overloaded

    vars_t& vars;
    IRBuilder<>& builder;
  };
  
  language_2_grammar( IRBuilder<>& ir) 
    : language_2_grammar::base_type(program), build(builder_helper(vars, ir)) {
    reserved_keywords = "var", "return";

    program = *(variable_declaration | assignment) >> return_statement;

    // we want to enforce the space after "return" so we must disable skipper with lexeme[]
    return_statement = lexeme["return" >> space] >> additive_expression[_val=build(_1)]>>';' ;
    
    additive_expression =
      multiplicative_expression               [_val=_1]
      >> *(
	   ('+' >> multiplicative_expression 
	    [_val= build(&IRBuilder<>::CreateAdd, _val, _1,"addtmp")])
	 |('-' >> multiplicative_expression 
	   [_val=build(&IRBuilder<>::CreateSub, _val, _1,"subtmp")])
	 )
	 ;
    multiplicative_expression =
      unary_expression               [_val=_1]
       >> *(
	   ('*' >> unary_expression[_val= build(&IRBuilder<>::CreateMul, _val, _1, "multmp")])
	   |('/' >> unary_expression [_val = build(&IRBuilder<>::CreateSDiv, _val, _1, "divtmp")])
	   )
      ;
    unary_expression =
      primary_expression[_val = _1]
      |   ('-' >> primary_expression[_val= build(&IRBuilder<>::CreateNeg, _1,"negtmp")])
      |   ('+' >> primary_expression[_val= _1])
      ;
    primary_expression =
      numeric_to_val             [_val=_1]
      | id_declared_var [_val=build(_1)]
      | '(' >> additive_expression  [_val=_1] >> ')'
      ;
    numeric_to_val = numeric_parser<value_t>::parser[_val=build(_1)];

    variable = id_declared_var[_val=build(_1)];

    id_declaration %= raw[lexeme[alpha >> *(alnum | '_')]] ;//lexeme disables skipping for >>

    id_declared_var = lexeme[ vars [_val = _1] // ditto for lexeme, id must be in vars
			      >> !(alnum | '_')]; // prevents partial match with only a prefix
			     
    variable_declaration = "var" >> !id_declared_var // disallow redeclaration of variables
				 >> !reserved_keywords
				 >> id_declaration [_a = build(_1)]
				 >> (';' | '=' >> assignment_rhs(_a));
    // id_declared_var returns the AllocaInst* of the variable
    assignment = id_declared_var [_a = _1] >> '=' >> assignment_rhs(_a);
    
    assignment_rhs = additive_expression[_a=_1] >> char_(';')[build(_r1, _a)];
    
  }

  symbols<char, unused_type> reserved_keywords;
  vars_t vars;

  boost::phoenix::function<builder_helper> build;
  
  rule<Iterator, Value*(), space_type> additive_expression,  multiplicative_expression
    , unary_expression, primary_expression,  numeric_to_val, variable;
  rule<Iterator, locals<AllocaInst*>, space_type> variable_declaration, assignment;
  rule<Iterator, AllocaInst*(), space_type> id_declared_var;
  rule<Iterator, std::string(), space_type> id_declaration;
  rule<Iterator, space_type> program, return_statement;
  rule<Iterator, void(AllocaInst*), locals<Value*>, space_type> assignment_rhs;
};
template<typename V>
bool exec_function(llvm::Module& module, std::string const& function_name="main")
{
  static bool init_done(false);
  if(!init_done){
    llvm::InitializeNativeTarget();
    init_done= true;
  }
  std::string ErrStr;
  llvm::ExecutionEngine* exec_engine_ptr= llvm::EngineBuilder(&module).setErrorStr(&ErrStr).create();
  if (!exec_engine_ptr) {
    std::cerr<<"Could not create ExecutionEngine:"<< ErrStr.c_str()<<std::endl;
    return false;
  }
  typedef V (*fun_ptr_t)(void);
  fun_ptr_t fun_ptr = 
    reinterpret_cast<fun_ptr_t>(exec_engine_ptr->getPointerToFunction(module.getFunction(function_name)));
  std::cout<<"result: "<<(*fun_ptr)()<<std::endl;
  return true;
}

int main(int argc, char* argv[]){
  typedef int value_t; // type used in arithmetic computations

  std::cin.unsetf(std::ios::skipws); //  Turn off white space skipping on the stream
  typedef std::string buffer_t;
  buffer_t buffer(std::istream_iterator<char>(std::cin), (std::istream_iterator<char>()));
  typedef buffer_t::const_iterator iter_t;
  iter_t iter(buffer.begin()), end(buffer.end());

  typedef language_2_grammar<value_t, iter_t> grammar_t;
  Module module("lang2", getGlobalContext());
  IRBuilder<> ir(BasicBlock::Create(getGlobalContext(), "entry",
						    cast<Function>(module.getOrInsertFunction("main", type<value_t>(), NULL))));
  grammar_t grammar(ir);
  bool r = phrase_parse(iter, end, grammar, space);
  if (r && iter == end) {
    std::cout<<"parsing succeded !\n";
    verifyModule(module, PrintMessageAction);
    module.dump();
    exec_function<value_t>(module, "main");
  } else {
    std::string rest(iter, end);
    std::cerr << "parsing failed\n" << "stopped at: \"" << rest << "\"\n";
  }
  return r ? 0 : 1 ;
}
