import syntaxtree.*;
import visitor.GJDepthFirst;
import java.io.*;
public class FirstVisitor extends GJDepthFirst<String,SymbolTable>{
	public String current_class;
	public String parent_Class;
	public boolean Inside_Fun;
	public String Fun_Name;
	public String FileName;
	FirstVisitor(){
		this.Inside_Fun=false;
		this.current_class=null;
		this.parent_Class=null;
	}





	/**
     * f0  -> "class"
     * f1  -> Identifier
     * f2  -> "{"
     * f3  -> "public"
     * f4  -> "static"
     * f5  -> "void"
     * f6  -> "main"
     * f7  -> "("
     * f8  -> "String"
     * f9  -> "["
     * f10 -> "]"
     * f11 -> Identifier()
     * f12 -> ")"
     * f13 -> "{"
     * f14 -> ( VarDeclaration() )*
     * f15 -> ( Statement() )*
     * f16 -> "}"
     * f17 -> "}"
     */
	public String visit(MainClass n,SymbolTable symtable) throws Exception{
		String y=n.f1.accept(this,symtable);
		this.FileName=y;/*Save FileName to emit to  FileName.ll*/
		return null;
	}


	/**
    * f0-> "class"
    * f1-> Identifier
    * f2-> "{"
    * f3->(VarDeclaration)
    * f4->(MethodDeclaration)
    * f5-> "}"
    */
    public String visit(ClassDeclaration n,SymbolTable sym) throws Exception{
    	String identifier=n.f1.accept(this,sym);
    	sym.My_map.put(identifier,new SymbolTable.ClassInfo());/*Put class to Hash Map and save all useful data to it*/
    	SymbolTable.ClassInfo ob =sym.My_map.get(identifier);
    	ob.Name=identifier;
    	this.current_class=identifier;
    	this.parent_Class=null;
    	n.f3.accept(this,sym);
    	n.f4.accept(this,sym);
        return null;
    }



    /**
    * fo->"class"
    * f1-> Identifier()
    * f2-> "extends"
    * f3-> Identifier()
    * f4-> "{"
    * f5-> (VarDeclaration)
    * f6-> (MethodDeclaration)
    * f7-> "}"
    */
    public String visit(ClassExtendsDeclaration n, SymbolTable symtable) throws Exception{
    	String identifier=n.f1.accept(this,symtable);
    	symtable.My_map.put(identifier,new SymbolTable.ClassInfo());/*Put class to Hash Map and save all useful data to it*/
    	SymbolTable.ClassInfo ob =symtable.My_map.get(identifier);
    	ob.Name=identifier;
    	this.current_class=identifier;
    	String par=n.f3.accept(this,symtable);
    	ob.parent_Class=par;
    	this.parent_Class=par;
    	n.f5.accept(this,symtable);
    	n.f6.accept(this,symtable);
    	return null; 
    }



     /**
    *f0 -> Type
    *f1 -> Identifier
    *f2 -> ";"
    */
    public String visit(VarDeclaration n,SymbolTable symtable) throws Exception{
    	String type=n.f0.accept(this,symtable);
    	String id=n.f1.accept(this,symtable);
    	SymbolTable.ClassInfo ob =symtable.My_map.get(this.current_class);
    	ob.Field_map.put(id,type);/* Variable Declaration*/
        return null;
    }





    /**
    * fo-> "public"
    * f1-> Type
    * f2-> Identifier
    * f3-> "("
    * f4-> (FormalParameterList)?
    * f5-> ")"
    * f6-> "{"
    * f7-> (VarDeclaration)
    * f8-> (Statement)
    * f9-> "return"
    * f10-> Expression
    * f11-> ";"
    * f12-> "}" 
    */
    public String visit(MethodDeclaration n,SymbolTable symtable) throws Exception{
    	String type=n.f1.accept(this,symtable);
       	String fun_name=n.f2.accept(this,symtable);
       	this.Fun_Name=fun_name;
       	SymbolTable.ClassInfo ob =symtable.My_map.get(this.current_class);
       	ob.Method_map.put(fun_name,new SymbolTable.MethodInfo());
       	if(this.parent_Class==null){
       		SymbolTable.MethodInfo f=ob.Method_map.get(fun_name);
       		f.name=fun_name;
       		f.return_type=type;
       		f.overriding=false;
       	}
       	else{
       		SymbolTable.MethodInfo f=ob.Method_map.get(fun_name);
       		f.name=fun_name;
       		f.return_type=type;
       		SymbolTable.ClassInfo a =symtable.My_map.get(this.parent_Class);
       		SymbolTable.MethodInfo f1=a.Method_map.get(fun_name);
       		if(f1==null)
       			f.overriding=false;
       		else
       			f.overriding=true;
       	}
       	n.f4.accept(this,symtable);
        return null;
    }

    /**
    * f0 ->IntegerArrayType
    	| BooleanArrayType
    */
    public String visit(ArrayType n,SymbolTable symtable) throws Exception{
    	return n.f0.accept(this,symtable);
    }

    /**
    * f0 ->"int" 
    * f1 -> "["
    * f2 -> "]"
    */
    public String visit(IntegerArrayType n,SymbolTable symtable) throws Exception{
    	return "int[]";
    }
    /**
    * f0 ->"boolean" 
    * f1 -> "["
    * f2 -> "]"
    */
    public String visit(BooleanArrayType n,SymbolTable symtable) throws Exception{
    	return "boolean[]";
    }
    /**
    * f0 -> "int"
    */
    public String visit(IntegerType n,SymbolTable symtable) throws Exception{
    	return "int";
    }

     /**
    * f0 -> "boolean"
    */
    public String visit(BooleanType n,SymbolTable symtable) throws Exception{
    	return "boolean";
    }

    /**
    * f0 -> ArrayType
    	 | 	BooleanType
    	 | IntegerType
    	 | Identifier
    */
    public String visit(Type n,SymbolTable symtable) throws Exception{
    	return n.f0.accept(this,symtable);
    }





/**
    *f0 -> Identifier()
    */
    public String visit(Identifier n,SymbolTable symtable) throws Exception{ return n.f0.toString(); }




      /**
    * f0-> FormalParameter
    * f1-> FormalParameterTail
    */
    public String visit(FormalParameterList n,SymbolTable symtable) throws Exception{
        n.f0.accept(this,symtable);
        n.f1.accept(this,symtable);
        return null;
    }

    /**
    * f0-> FormalParameterTerm
    */
    public String visit(FormalParameterTail n,SymbolTable symtable) throws Exception{
        n.f0.accept(this,symtable);
        return null;
    }

    /**
    * f0-> ","
    * f1-> FormalParameter
    */
    public String visit(FormalParameterTerm n,SymbolTable symtable) throws Exception{
        n.f1.accept(this,symtable);
        return null;
    }


 	/**
    * f0-> Type
    * f1-> Identifier
    */
    public String visit(FormalParameter n,SymbolTable symtable) throws Exception{
       	String type=n.f0.accept(this,symtable);
       	String ide=n.f1.accept(this,symtable);
       	SymbolTable.ClassInfo ob =symtable.My_map.get(this.current_class);
       	SymbolTable.MethodInfo f=ob.Method_map.get(this.Fun_Name);
      	f.parameters.put(ide,type);/*Put prototype of function to HashMap*/
        return null;
    }

}