import syntaxtree.*;
import visitor.GJDepthFirst;
import java.util.Map;
import java.io.*;
public class MiniJavatoLLVM extends GJDepthFirst<String,SymbolTable>{
	public String FileName;
	public BufferedWriter bw;
	public String Current_Class;
	public String parent_Class;
	public String Name_Fun;
	public int Current_Register_Available_Number;
	public int val_nsz_ok;
	public String Argu;
	public int val_nsz_err;
	public String Current;
	public String newClass;
	public String Type_Value;
	public String Object_New;
	public int oob_ok;
	public int oob_err;
	public boolean New_Object;
	public boolean Place;
	public int oob;
	public int if_then;
	public String prim;
	public int if_else;
	public int loop;
	public boolean re;
	public int if_end;
	public String State_re;
	public boolean this_item;
	public String type_on_arrayassignment;
	public int expr_res;
	MiniJavatoLLVM(){
		this.parent_Class=null;
		this.Current=null;
		this.this_item=false;
		this.Argu="";
		this.State_re=null;
		this.New_Object=false;
		this.re=false;
		this.oob=0;
		this.Place=false;
		this.prim=null;
		this.type_on_arrayassignment=null;
		this.newClass=null;
		this.if_else=0;
		this.expr_res=0;
		this.if_end=0;
		this.Name_Fun=null;
		this.Type_Value=null;
		this.Object_New=null;
		this.val_nsz_ok=0;
		this.loop=0;
		this.oob_ok=0;
		this.oob_err=0;
		this.val_nsz_err=0;
		this.Current_Register_Available_Number=0;
		this.Current_Class=null;
		this.FileName=null;
	}
	public void emit(String message) throws Exception{
		PrintWriter pw=new PrintWriter(new FileOutputStream(new File(this.FileName+".ll"),true));
		if(pw==null)
			throw new Exception("Error:PrintWriter");
		pw.append(message);
		pw.close();
	}
	public int position_Function(SymbolTable symtable,String id1,String class_name) throws Exception{
		int pos=0;
		SymbolTable.Info k=symtable.Vmap.get(class_name);
		if(k==null)
			return -1;
		for(Map.Entry<String, Integer> entry : k.Method_map.entrySet()){
			String e=entry.getKey();
			if(e.equals(id1))
				return pos;
			pos+=1;
		}
		return pos;
	}
	public String Class_Member(SymbolTable symtable,String var,String class_name){/*Check if this Variable belongs to Field Map of The Class*/
		String type=null;
		SymbolTable.Info k=symtable.Vmap.get(class_name);
		if(k==null)
			return null;
		for(Map.Entry<String, Integer> entry : k.variable.entrySet()){
			String e1=entry.getKey();
			int e2=entry.getValue();
			if(e1.equals(var)){
				while(true){
					SymbolTable.ClassInfo w=symtable.My_map.get(class_name);
					if(w==null)
						break;
					for(Map.Entry<String,String> a : w.Field_map.entrySet()){
						String n1=a.getValue();
						String n2=a.getKey();
						if(var.equals(n2)){
							type=n1;
							if(type.equals("int"))
								return "i32";
							else if(type.equals("int[]"))
								return "i32*";
							else if(type.equals("boolean"))
								return "i1";
							else 
								return "i8*";
						}
					}
					class_name=w.parent_Class;	
				}
			}
		}
		return type;
	}
	public int position(SymbolTable sym,String var,String class_name){
		SymbolTable.Info k=sym.Vmap.get(class_name);
		if(k==null)
			return -1;
		int coun=0;
		for(Map.Entry<String, Integer> entry : k.variable.entrySet()){
			String e1=entry.getKey();
			int e2=entry.getValue();
			if(e1.equals(var)){
				coun=8+e2;
				return coun;
			}
		}
		return -1;
	}
	public void emit_define_methods() throws Exception{/*Emit <<standar>> Data*/
		emit("declare i8* @calloc(i32, i32)\n");
		emit("declare i32 @printf(i8*, ...)\n");
		emit("declare void @exit(i32)\n\n");
		emit("@_cint = constant [4 x i8] c\"%d\\0a\\00\"\n");
		emit("@_cOOB = constant [15 x i8] c\"Out of bounds\\0a\\00\"\n");
		emit("@_cNSZ = constant [15 x i8] c\"Negative size\\0a\\00\"\n");
		emit("define void @print_int(i32 %i) {\n");
		emit("\t%_str = bitcast [4 x i8]* @_cint to i8*\n");
		emit("\tcall i32 (i8*, ...) @printf(i8* %_str, i32 %i)\n");
		emit("\tret void\n");
		emit("}\n\n");
		emit("define void @throw_oob() {\n");
		emit("\t%_str = bitcast [15 x i8]* @_cOOB to i8*\n");
		emit("\tcall i32 (i8*, ...) @printf(i8* %_str)\n");
		emit("\tcall void @exit(i32 1)\n");
		emit("\tret void\n");
		emit("}\n\n");
		emit("define void @throw_nsz() {\n");
		emit("\t%_str = bitcast [15 x i8]* @_cNSZ to i8*\n");
		emit("\tcall i32 (i8*, ...) @printf(i8* %_str)\n");
		emit("\tcall void @exit(i32 1)\n");
		emit("\tret void\n");
		emit("}\n\n");
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
		this.Type_Value="MainClass";
		String id=n.f1.accept(this,symtable);
		this.Current_Class=id;
		this.FileName=id;
		emit("@."+this.FileName+"_vtable = global [0 x i8*] []\n\n");
		emit_define_methods();
		emit("define i32 @main() {\n");
		symtable.Decl.put(this.Current_Class,new SymbolTable.VarMap());
		n.f14.accept(this,symtable);
		n.f15.accept(this,symtable);
		emit("\tret i32 0\n");
		emit("}\n");
		this.Current_Register_Available_Number=0;
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
    public String visit(ClassDeclaration n,SymbolTable symtable) throws Exception{
    	this.Type_Value="ClassDeclaration";
    	this.Current_Class=n.f1.accept(this,symtable);
    	symtable.Decl.put(this.Current_Class,new SymbolTable.VarMap());
    	n.f4.accept(this,symtable);
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
    	this.Type_Value="ClassExtendsDeclaration";
    	this.Current_Class=n.f1.accept(this,symtable);
    	symtable.Decl.put(this.Current_Class,new SymbolTable.VarMap());
    	this.parent_Class=n.f3.accept(this,symtable);
    	n.f6.accept(this,symtable);
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
       	emit("define ");
       	this.Type_Value="MethodDeclaration";
       	String type=n.f1.accept(this,symtable);
       	String ret=null;
       	if(type.equals("int")){
       		emit("i32");
       		ret="i32";
       	}
       	else if(type.equals("boolean")){
       		emit("i1");
       		ret="i1";
       	}
       	else if(type.equals("boolean[]")){
       		ret="i8*";
       		emit("i8*");
       	}
       	else if (type.equals("int[]")){
       		ret="i32*";
       		emit("i32*");
       	}
       	else{ 
       		ret="i8*";
       		emit("i8*");
       	}
       	emit(" @"+this.Current_Class+".");
       	this.Type_Value="MethodDeclaration";
       	String name_fun=n.f2.accept(this,symtable);
       	this.Name_Fun=name_fun;
       	emit(name_fun);
       	emit("(i8* %this");
       	String class_name=this.Current_Class;
    	SymbolTable.ClassInfo a=symtable.My_map.get(class_name);
    	SymbolTable.MethodInfo p =a.Method_map.get(name_fun);
       	int coun=0;
       	for(Map.Entry<String,String>  k : p.parameters.entrySet())
       		coun+=1;
       	if(coun==0)
       		emit(") {\n");
       	else{
       		emit(",");
       		int val=0;
       		for(Map.Entry<String,String>  k : p.parameters.entrySet()){
       			String type1=k.getValue();
       			String id=k.getKey();
       			if(type1.equals("int"))
       				emit("i32 ");
       			else if(type1.equals("boolean"))
       				emit("i1 ");
       			else if(type1.equals("int[]"))
       				emit("i32* ");
       			else if(type1.equals("boolean[]"))
       				emit("i8* ");
       			else
       				emit("i8* ");
       			emit("%."+id);
       			val+=1;
       			if(val!=coun)
       				emit(",");
       			else 
       				emit(")");
       		}
       		emit(" {\n");
       	}
       	n.f4.accept(this,symtable);
       	n.f7.accept(this,symtable);
       	n.f8.accept(this,symtable);
       	this.re=true;
       	n.f10.accept(this,symtable);
       	emit("\tret "+ret+" "+this.Current+"\n");
       	emit("\n}\n");
       	this.re=false;
       	this.Current_Register_Available_Number=0;
        return null;
    }

   
    /**
    *f0 -> Type()
    *f1 -> Identifier()
    *f2 -> ";"
    */
    public String visit(VarDeclaration n,SymbolTable symtable) throws Exception{
    	String type=n.f0.accept(this,symtable);
    	this.Type_Value="VarDeclaration";
    	String id=n.f1.accept(this,symtable);
    	SymbolTable.VarMap k=symtable.Decl.get(this.Current_Class);
    	this.Type_Value="VarDeclaration";
    	k.variable.put(id,type);
    	emit("\t%"+id+" = alloca ");
    	if(type.equals("int"))
    		emit("i32\n");
    	else if(type.equals("boolean"))
    		emit("i1\n");
    	else if(type.equals("int[]"))
    		emit("i32*\n");
    	else if(type.equals("boolean[]"))
    		emit("i8*\n");
    	else
    		emit("i8*\n");
        return null;
    }

   	/**
	*f0     ->  Block
			|	AssignmentStatement
			|	ArrayAssignmentStatement
			|	IfStatement
			|	WhileStatement
			|	PrintStatement
	*/
	public String visit(Statement n ,SymbolTable symtable) throws Exception{
		n.f0.accept(this,symtable);
		return null;
	}



	/**
	* f0 -> "{"
	* f1 -> (Statement)?
	* f2 -> "}"
	*/
	public String visit(Block n,SymbolTable symtable) throws Exception{
		n.f1.accept(this,symtable);
		return null;
	} 
	
    /**
	* f0 -> Identifier
	* f1 -> "="
	* f2 -> Expression
	* f3 -> ";"
	*/
	public String visit(AssignmentStatement n,SymbolTable symtable) throws Exception{
		this.Type_Value="AssignmentStatement";
		this.Place=false;
		n.f0.accept(this,symtable);
		this.Place=true;
		String expr1=this.Current;
		this.Object_New=this.Current;
		this.Object_New=expr1;
		n.f2.accept(this,symtable);
		String type2=this.Type_Value;
		String expr2=this.Current;
		if(type2.equals("boolean")){
			String found=Class_Member(symtable,expr1,this.Current_Class);
			if(found==null){
				if(this.Current.equals("0"))
					emit("\tstore i1 0, i1* %"+expr1+"\n");
				else if(this.Current.equals("1"))
					emit("\tstore i1 1, i1* %"+expr1+"\n");
			}
			else{
				int valu1=position(symtable,expr1,this.Current_Class);
				emit("\t%_"+this.Current_Register_Available_Number+" = getelementptr i8, i8* %this, i32 "+valu1+"\n");
				int f1=this.Current_Register_Available_Number;
				this.Current_Register_Available_Number+=1;
				emit("\t%_"+this.Current_Register_Available_Number+" = bitcast i8* %_"+f1+" to "+found+"*\n");
				int f2=this.Current_Register_Available_Number;
				this.Current_Register_Available_Number+=1;
				if(this.Current.equals("0"))
					emit("\tstore i1 0, i1* %_"+f2+"\n");
				else if(this.Current.equals("1"))
					emit("\tstore i1 1, i1* %_"+f2+"\n");
			}
		}
		else if(type2.equals("Identifier")){
			String found=Class_Member(symtable,expr1,this.Current_Class);
			if(found==null){
				String timh=expr2;
				emit("\tstore i32 "+timh+",i32* %"+expr1+"\n");
			}
			else{
				int valu1=position(symtable,expr1,this.Current_Class);
				String g=found;
				emit("\t%_"+this.Current_Register_Available_Number+" = getelementptr i8, i8* %this, i32 "+valu1+"\n");
				int f1=this.Current_Register_Available_Number;
				this.Current_Register_Available_Number+=1;
				emit("\t%_"+this.Current_Register_Available_Number+" = bitcast i8* %_"+f1+" to "+g+"*\n");
				int f2=this.Current_Register_Available_Number;
				this.Current_Register_Available_Number+=1;
				emit("\tstore i32 "+expr2+", i32* %_"+f2+"\n");
			}
		}
		else if(type2.equals("Inside-Interger")){
			if(this.New_Object==false)
				emit("\tstore i32* %_"+this.Current_Register_Available_Number+", i32** %"+expr1+"\n");
			this.Current_Register_Available_Number+=1;
		}
		else if(type2.equals("ThisExpression")){
			String found=Class_Member(symtable,expr1,this.Current_Class);
			if(found==null)
				emit("\tstore i8* %this, i8** %"+expr1+"\n");
			else{
				int valu1=position(symtable,expr1,this.Current_Class);
				String g=found;
				emit("\t%_"+this.Current_Register_Available_Number+" = getelementptr i8, i8* %this, i32 "+valu1+"\n");
				int f1=this.Current_Register_Available_Number;
				this.Current_Register_Available_Number+=1;
				emit("\t%_"+this.Current_Register_Available_Number+" = bitcast i8* %_"+f1+" to "+g+"*\n");
				int f2=this.Current_Register_Available_Number;
				this.Current_Register_Available_Number+=1;
				emit("\tstore i8* %this, i8** %_"+f2+"\n");
			}
		}
		else if(type2.equals("Inside-Boolean"))
			this.Current_Register_Available_Number+=2;
		else if(type2.equals("Variable")){
			String found=Class_Member(symtable,expr1,this.Current_Class);
			if(found==null){
				String type=symtable.Value_Type(symtable,expr1,this.Current_Class,this.Name_Fun);
				if(type.equals("i32"))
						emit("\tstore i32 "+this.Current+", i32* %"+expr1+"\n");
				else if(type.equals("i32*"))
					emit("\tstore i32* "+this.Current+", i32** %"+expr1+"\n");
				else if(type.equals("i1"))
					emit("\tstore i1 "+this.Current+", i1* %"+expr1+"\n");
				else
					emit("\tstore i8* "+this.Current+", i8** %"+expr1+"\n");
			}
			else{
				int valu1=position(symtable,expr1,this.Current_Class);
				emit("\t%_"+this.Current_Register_Available_Number+" = getelementptr i8, i8* %this, i32 "+valu1+"\n");
				int f1=this.Current_Register_Available_Number;
				this.Current_Register_Available_Number+=1;
				emit("\t%_"+this.Current_Register_Available_Number+" = bitcast i8* %_"+f1+" to "+found+"*\n");
				int f2=this.Current_Register_Available_Number;
				this.Current_Register_Available_Number+=1;
				if(found.equals("i32*"))
					emit("\tstore i32* "+this.Current+", i32** %_"+f2+"\n");
				else if(found.equals("i32"))
					emit("\tstore i32 "+this.Current+", i32* %_"+f2+"\n");
				else if(found.equals("i1"))
					emit("\tstore i1 "+this.Current+", i1* %_"+f2+"\n");
				else
					emit("\tstore i8* "+this.Current+", i8** %_"+f2+"\n");
			}
			
		}
		else{
			String found1=Class_Member(symtable,expr1,this.Current_Class);
			if(found1==null){
				String type=symtable.Value_Type(symtable,expr1,this.Current_Class,this.Name_Fun);
				if(type.equals("i32"))
					emit("\tstore i32 "+expr2+", i32* %"+expr1+"\n");
				else if(type.equals("i32*"))
					emit("\tstore i32* "+expr2+", i32** %"+expr1+"\n");
				else if(type.equals("i1"))
					emit("\tstore i1 "+expr2+", i1* %"+expr1+"\n");
				else
					emit("\tstore i8* "+expr2+", i8** %"+expr1+"\n");
				this.Current_Register_Available_Number+=1;
			}
			else{
				int valu1=position(symtable,expr1,this.Current_Class);
				emit("\t%_"+this.Current_Register_Available_Number+" = getelementptr i8, i8* %this, i32 "+valu1+"\n");
				int f1=this.Current_Register_Available_Number;
				this.Current_Register_Available_Number+=1;
				emit("\t%_"+this.Current_Register_Available_Number+" = bitcast i8* %_"+f1+" to "+found1+"*\n");
				int f2=this.Current_Register_Available_Number;
				this.Current_Register_Available_Number+=1;
				if(found1.equals("i32*"))
					emit("\tstore i32* "+expr2+", i32** %_"+f2+"\n");
				else if(found1.equals("i32"))
					emit("\tstore i32 "+expr2+", i32* %_"+f2+"\n");
				else if(found1.equals("i1"))
					emit("\tstore i1 "+expr2+", i1* %_"+f2+"\n");
				else
					emit("\tstore i8* "+expr2+", i8** %_"+f2+"\n");
			}
		}
		return null;
	}
	

	/**
	* f0 -> Identifier
	* f1 -> "["
	* f2 -> Expression
	* f3 -> "]"
	* f4 -> "="
	* f5 -> Expression
	* f6 -> ";"
	*/
	public String visit(ArrayAssignmentStatement n,SymbolTable symtable) throws Exception{
		this.Type_Value="ArrayAssignmentStatement";
		n.f0.accept(this,symtable);
		String id0=this.Current;
		if(this.type_on_arrayassignment.equals("i32*")){
			if(this.this_item==false){
				String  f=this.Current;
				emit("\t%_"+this.Current_Register_Available_Number+" = load i32, i32 *"+id0+"\n");
				int f1=this.Current_Register_Available_Number;
				this.Current_Register_Available_Number+=1;
				n.f2.accept(this,symtable);
				emit("\t%_"+this.Current_Register_Available_Number+" = icmp sge i32 "+this.Current+" , 0\n");
				int f2=this.Current_Register_Available_Number;
				this.Current_Register_Available_Number+=1;
				emit("\t%_"+this.Current_Register_Available_Number+" = icmp slt i32 "+this.Current+", %_"+f1+"\n");
				int f3=this.Current_Register_Available_Number;
				this.Current_Register_Available_Number+=1;
				emit("\t%_"+this.Current_Register_Available_Number+" = and i1 %_"+f2+" , %_"+f3+"\n");
				emit("\tbr i1 %_"+this.Current_Register_Available_Number+" , label %oob_ok_"+this.oob_ok+" , label %oob_err_"+this.oob_err+"\n");
				emit("\toob_err_"+this.oob_err+":\n");
				emit("\tcall void @throw_oob()\n");
				emit("\tbr label %oob_ok_"+this.oob_ok+"\n");
				emit("\toob_ok_"+this.oob_ok+":\n");
				this.Current_Register_Available_Number+=1;
				emit("\t%_"+this.Current_Register_Available_Number+" = add i32 1,"+this.Current+"\n");
				int f4=this.Current_Register_Available_Number;
				this.Current_Register_Available_Number+=1;
				emit("\t%_"+this.Current_Register_Available_Number+" = getelementptr i32, i32* "+f+" , i32 %_"+f4+"\n");
				int y=this.Current_Register_Available_Number;
				this.Current_Register_Available_Number+=1;
				this.oob_ok+=3;
				this.oob_err+=3;
				n.f5.accept(this,symtable);
				emit("\tstore i32 "+this.Current+" , i32* %_"+y+"\n");
				this.oob_ok+=1;
				this.oob_err+=1;
			}
			else{
				emit("\t%_"+this.Current_Register_Available_Number+" = load i32, i32 *"+id0+"\n");
				int f1=this.Current_Register_Available_Number;
				this.Current_Register_Available_Number+=1;
				n.f2.accept(this,symtable);
				String size=this.Current;
				emit("\t%_"+this.Current_Register_Available_Number+"  = icmp sge i32 "+size+" , 0\n");
				int f2=this.Current_Register_Available_Number;
				this.Current_Register_Available_Number+=1;
				emit("\t%_"+this.Current_Register_Available_Number+"  = icmp slt i32 "+size+" , %_"+f1+"\n");
				int f3=this.Current_Register_Available_Number;
				this.Current_Register_Available_Number+=1;
				emit("\t%_"+this.Current_Register_Available_Number+" = and i1 %_"+ f2+" , %_"+f3+"\n");
				emit("\tbr i1 %_"+this.Current_Register_Available_Number+", label %oob_ok_"+this.oob_ok+", label %oob_err_"+this.oob_err+"\n");
				emit("\t oob_err_"+this.oob_err+":\n");
				emit("\tcall void @throw_oob()\n");
				emit("\tbr label %oob_ok_"+this.oob_ok+"\n");
				emit("\t oob_ok_"+this.oob_ok+":\n");
				this.Current_Register_Available_Number+=1;
				emit("\t%_"+this.Current_Register_Available_Number+"  = add i32 1, "+size+"\n");
				int f6=this.Current_Register_Available_Number;
				this.Current_Register_Available_Number+=1;
				emit("\t%_"+this.Current_Register_Available_Number+" = getelementptr i32, i32* "+id0+ ", i32 %_"+f6+"\n");
				int t=this.Current_Register_Available_Number;
				this.Current_Register_Available_Number+=1;
				this.oob_ok+=3;
				this.oob_err+=3;
				n.f5.accept(this,symtable);
				String e=this.Current;
				emit("\tstore i32 "+e+", i32* %_"+t+"\n");
				this.Current_Register_Available_Number+=1;
				this.oob_ok+=1;
				this.oob_err+=1;
			}
		}
		else if(this.type_on_arrayassignment.equals("i8*")){
			if(this.this_item==false){
				String f=this.Current;
				emit("\t%_"+this.Current_Register_Available_Number+"  = bitcast i8* "+f+"  to i32*\n");
				int f1=this.Current_Register_Available_Number;
				this.Current_Register_Available_Number+=1;
				emit("\t%_"+this.Current_Register_Available_Number+" = load i32, i32* %_"+f1+"\n");
				int f2=this.Current_Register_Available_Number;
				this.Current_Register_Available_Number+=1;
				n.f2.accept(this,symtable);
				String size=this.Current;
				emit("\t%_"+this.Current_Register_Available_Number+"  = icmp sge i32 "+size+" , 0\n");
				int f3=this.Current_Register_Available_Number;
				this.Current_Register_Available_Number+=1;
				emit("\t%_"+this.Current_Register_Available_Number+" = icmp slt i32 "+size+" , %_"+f2+"\n");
				int f4=this.Current_Register_Available_Number;
				this.Current_Register_Available_Number+=1;
				emit("\t%_"+this.Current_Register_Available_Number+" = and i1 %_"+f3+" , %_"+f4+"\n");
				emit("\tbr i1 %_"+this.Current_Register_Available_Number+", label %oob_ok_"+this.oob_ok+", label %oob_err_"+this.oob_err+"\n");
				this.Current_Register_Available_Number+=1;
				emit("\t oob_err_"+this.oob_err+":\n");
				emit("\tcall void @throw_oob()\n");
				emit("\tbr label %oob_ok_"+this.oob_ok+"\n");
				emit("\t oob_ok_"+this.oob_ok+":\n");
				emit("\t%_"+this.Current_Register_Available_Number+" = add i32 4, "+size+"\n");
				int g=this.Current_Register_Available_Number;
				this.Current_Register_Available_Number+=1;
				n.f5.accept(this,symtable);
				emit("\t%_"+this.Current_Register_Available_Number+" = zext i1 "+this.Current+" to i8\n");
				int f5=this.Current_Register_Available_Number;
				this.Current_Register_Available_Number+=1;
				emit("\t%_"+this.Current_Register_Available_Number+" = getelementptr i8, i8* "+f+ ", i32 %_"+g+"\n");
				int f6=this.Current_Register_Available_Number;
				this.Current_Register_Available_Number+=1;
				emit("\tstore i8 %_"+f5+", i8* %_"+f6+"\n");
				this.oob_err+=1;
				this.oob_ok+=1;
			}
			else{
				String f=this.Current;
				emit("\t%_"+this.Current_Register_Available_Number+" = load i8**, i8** "+id0+"\n");
				int f1=this.Current_Register_Available_Number;
				this.Current_Register_Available_Number+=1;
				emit("\t%_"+this.Current_Register_Available_Number+" = load i8, i8*"+f1+"\n");
				int f2=this.Current_Register_Available_Number;
				this.Current_Register_Available_Number+=1;
				n.f2.accept(this,symtable);
				String size=this.Current;
				emit("\t%_"+this.Current_Register_Available_Number+" = icmp ult i32 "+size+" , %_"+f2+"\n");
				int start1=this.oob+1;
				int start2=this.oob+2;
				int start3=this.oob+3;
				emit("\tbr i1 %_"+this.Current_Register_Available_Number+", label %oob"+start1+", label %oob"+start2+"\n");
				emit("\toob"+start1+":\n");
				emit("\t%_"+this.Current_Register_Available_Number+"= add i32 "+size+",1\n");
				int f3=this.Current_Register_Available_Number;
				this.Current_Register_Available_Number+=1;
				emit("\t%_"+this.Current_Register_Available_Number+"  = getelementptr i32, i32* %_"+f+", i32 %_"+f3+"\n");
				int f4=this.Current_Register_Available_Number;
				this.Current_Register_Available_Number+=1;
				n.f5.accept(this,symtable);
				String result=this.Current;
				emit("\tstore i32 "+result+" , i32* %_"+f4+"\n");
				emit("\tbr label %oob"+start3+"\n");
				emit("\toob"+start2+"\n");
				emit("\tcall void @throw_oob()\n");
				emit("\tbr label %oob"+start3+"\n");
				emit("\toob"+start3+"\n");
				this.oob+=4;
			}
		}
		else 
			throw new Exception("Wrong type");
		return null;
	}
	
	
	

    
	/**
	* f0 -> "if"
	* f1 -> "("
	* f2 -> Expression
	* f3 -> ")"
	* f4 -> Statement
	* f5 -> "else"
	* f6 -> Statement
	*/
	public String visit(IfStatement n ,SymbolTable symtable) throws Exception{
		n.f2.accept(this,symtable);
		String val=this.Current;
		int n1=this.if_then;
		int n2=this.if_else;
		int n3=this.if_end;
		emit("\tbr i1 "+val+", label %if_then_"+n1+", label %if_else_"+n2+"\n");
		emit("\tif_else_"+n1+":"+"\n");
		this.if_else+=10;
		this.if_then+=10;
		this.if_end+=10;
		n.f6.accept(this,symtable);
		this.if_else+=10;
		this.if_then+=10;
		this.if_end+=10;
		emit("\tbr label %if_end_"+n3+"\n");
		emit("\tif_then_"+n1+":\n");
		n.f4.accept(this,symtable);
		this.if_else+=10;
		this.if_then+=10;
		this.if_end+=10;
		emit("\tbr label %if_end_"+n3+"\n");
		emit("\tif_end_"+n3+":\n");
		return null;
	}

	/**
	* f0 -> "System.out.println"
	* f1 -> "("
	* f2 -> Expression
	* f3 -> ")"
	* f4 -> ";"
	*/
	public String visit(PrintStatement n ,SymbolTable symtable) throws Exception{
		n.f2.accept(this,symtable);
		if(this.Type_Value.equals("Identifier")){
			String result="i32 "+this.Current;
			emit("\tcall void (i32) @print_int("+result+")\n");
		}
		else if(this.Type_Value.equals("Variable")){
			String result="i32 "+this.Current;
			emit("\tcall void (i32) @print_int("+result+")\n");
		}
		else{
			String val1=this.Current;
			String result="i32 "+val1;
			emit("\tcall void (i32) @print_int("+result+")\n");
		}
		return null;
	}

	/**
	* f0 -> "while"
	* f1 -> "("
	* f2 -> Expression
	* f3 -> ")"
	* f4 -> Statement
	*/
	public String visit(WhileStatement n ,SymbolTable symtable) throws Exception{
		emit("\tbr label %loop"+this.loop+"\n");
		int start=this.loop;
		emit("loop"+this.loop+":\n");
		n.f2.accept(this,symtable);
		String val=this.Current;
		int br1=this.loop+1;
		int br2=this.loop+2;
		emit("\tbr i1 "+val+", label %loop"+br1+", label %loop"+br2+"\n");
		emit("loop"+br1+":\n");
		this.loop+=4;
		n.f4.accept(this,symtable);
		emit("\tbr label %loop"+start+"\n");
		emit("loop"+br2+":\n");
		return null;
	}




	



	/**
	* f0 ->     IntergerLiteral	
	    	|	TrueLiteral
			|	FalseLiteral
			|	Identifier
			|	ThisExpression
			|	ArrayAllocationExpression
			|	AllocationExpression
			|	BracketExpression
	*/
	public String visit(PrimaryExpression n,SymbolTable symtable) throws Exception{
		n.f0.accept(this,symtable);
		return null;
	}




	



	/**
	* f0 -> NotExpression
		| PrimaryExpression
	*/
	public String visit(Clause n,SymbolTable symtable) throws Exception{
		n.f0.accept(this,symtable);
		return null;
	}


	/**
	* f0 -> BooleanArrayAllocationExpression
		  | IntegerArrayAllocationExpression
	*/
	public String visit(ArrayAllocationExpression n,SymbolTable symtable) throws Exception{
		n.f0.accept(this,symtable);
		return null;
	}
	/**
	* f0 -> "new"
	* f1 -> "boolean"
	* f2 -> "["
	* f3 -> Expression
	* f4 -> "]"
	*/
	public String visit(BooleanArrayAllocationExpression n,SymbolTable symtable) throws Exception{
		n.f3.accept(this,symtable);
		String id=this.Object_New;
		String found=Class_Member(symtable,id,this.Current_Class);
		if(found==null){
			if(this.Type_Value.equals("Identifier")){
				String value=this.Current;
				emit("\t%_"+this.Current_Register_Available_Number+"= add i32 4, "+value);
				emit("\n");
				int timh1=this.Current_Register_Available_Number;
				this.Current_Register_Available_Number+=1;
				emit("\t%_"+this.Current_Register_Available_Number+" = icmp sge i32 %_"+timh1+" , 4");
				emit("\n");
				emit("\tbr i1 %_"+this.Current_Register_Available_Number+",  label %nsz_ok_"+this.val_nsz_ok+", label %nsz_err_"+ this.val_nsz_err);
				emit("\n");
				emit("\tnsz_err_"+this.val_nsz_err+":");
				emit("\n");
				emit("\tcall void @throw_nsz()");
				emit("\n");
				emit("\tbr label %nsz_ok_"+this.val_nsz_ok);
				emit("\n");
				emit("\tnsz_ok_"+this.val_nsz_ok+":");
				emit("\n");
				this.val_nsz_ok+=1;
				this.val_nsz_err+=1;
				this.Current_Register_Available_Number+=1;
				emit("\t%_"+this.Current_Register_Available_Number+" = call i8* @calloc(i32 1,i32 %_"+timh1+")\n");
				int timh2=this.Current_Register_Available_Number;
				this.Current_Register_Available_Number+=1;
				emit("\t%_"+this.Current_Register_Available_Number+" =  bitcast i8* %_"+timh2+" to i32*\n");
				emit("\tstore i32 "+value+" , i32* %_"+this.Current_Register_Available_Number+"\n");
				this.Type_Value="Inside-Boolean";
				this.Current_Register_Available_Number=timh2;
				this.Current_Register_Available_Number+=1;
				emit("\tstore  i8* %_"+timh2+", i8** %"+this.Object_New+"\n");
				
			}
			else{
				String value=this.Current;
				emit("\t%_"+this.Current_Register_Available_Number+" = icmp slt i32 "+value+" , 0");
				emit("\n");
				emit("\tbr i1 %_"+this.Current_Register_Available_Number+",  label %nsz_ok_"+this.val_nsz_ok+", label %nsz_err_"+ this.val_nsz_err);
				emit("\n");
				emit("\tnsz_err_"+this.val_nsz_err+":");
				emit("\n");
				emit("\tcall void @throw_nsz()");
				emit("\n");
				emit("\tbr label %nsz_ok_"+this.val_nsz_ok);
				emit("\n");
				emit("\tnsz_ok_"+this.val_nsz_ok+":");
				emit("\n");
				this.val_nsz_ok+=1;
				this.val_nsz_err+=1;
				this.Current_Register_Available_Number+=1;
				emit("\t%_"+this.Current_Register_Available_Number+" = call i8* @calloc(i32 1,i32 "+value+")\n");
				int timh2=this.Current_Register_Available_Number;
				this.Current_Register_Available_Number+=1;
				emit("\t%_"+this.Current_Register_Available_Number+" =  bitcast i8* %_"+timh2+" to i32*\n");
				int timh5=this.Current_Register_Available_Number;
				this.Current_Register_Available_Number+=1;
				emit("\tstore i32 "+value+" , i32* %_"+timh5+"\n");
				emit("\tstore i8* %_"+timh2+", i8** %"+this.Object_New+"\n");
				this.Type_Value="Inside-Boolean";
				
			}
		}
		else{
			int valu1=position(symtable,id,this.Current_Class);
			if(this.Type_Value.equals("Identifier")){
				String value=this.Current;
				emit("\t%_"+this.Current_Register_Available_Number+"= add i32 4, "+value);
				emit("\n");
				int timh1=this.Current_Register_Available_Number;
				this.Current_Register_Available_Number+=1;
				emit("\t%_"+this.Current_Register_Available_Number+" = icmp slt i32 %_"+timh1+" , 4");
				emit("\n");
				emit("\tbr i1 %_"+this.Current_Register_Available_Number+",  label %nsz_ok_"+this.val_nsz_ok+", label %nsz_err_"+ this.val_nsz_err);
				emit("\n");
				emit("\tnsz_err_"+this.val_nsz_err+":");
				emit("\n");
				emit("\tcall void @throw_oob()");
				emit("\n");
				emit("\tbr label %nsz_ok_"+this.val_nsz_ok);
				emit("\n");
				emit("\tnsz_ok_"+this.val_nsz_ok+":");
				emit("\n");
				this.val_nsz_ok+=1;
				this.val_nsz_err+=1;
				this.Current_Register_Available_Number+=1;
				emit("\t%_"+this.Current_Register_Available_Number+" = call i8* @calloc(i32 1,i32 %_"+timh1+")\n");
				int timh2=this.Current_Register_Available_Number;
				this.Current_Register_Available_Number+=1;
				emit("\t%_"+this.Current_Register_Available_Number+" =  bitcast i8* %_"+timh2+" to i32*\n");
				int ft=this.Current_Register_Available_Number;
				emit("\tstore i32 "+value+" , i32* %_"+this.Current_Register_Available_Number+"\n");
				this.Type_Value="Inside-Boolean";
				this.Current_Register_Available_Number+=1;
				emit("\t%_"+this.Current_Register_Available_Number+" = getelementptr i8, i8* %this, i32 "+valu1+"\n");
				int f1=this.Current_Register_Available_Number;
				this.Current_Register_Available_Number+=1;
				emit("\t%_"+this.Current_Register_Available_Number+" = bitcast i8* %_"+f1+" to "+found+"*\n");
				int f2=this.Current_Register_Available_Number;
				this.Current_Register_Available_Number+=1;
				emit("\tstore i8* %_"+timh2+", i8** %_"+f2+"\n");
			}
			else{
				String value=this.Current;
				emit("\t%_"+this.Current_Register_Available_Number+" = icmp slt i32 "+value+" , 4");
				emit("\n");
				emit("\tbr i1 %_"+this.Current_Register_Available_Number+",  label %nsz_ok_"+this.val_nsz_ok+", label %nsz_err_"+ this.val_nsz_err);
				emit("\n");
				emit("\tnsz_err_"+this.val_nsz_err+":");
				emit("\n");
				emit("\tcall void @throw_oob()");
				emit("\n");
				emit("\tbr label %nsz_ok_"+this.val_nsz_ok);
				emit("\n");
				emit("\tnsz_ok_"+this.val_nsz_ok+":");
				emit("\n");
				this.val_nsz_ok+=1;
				this.val_nsz_err+=1;
				this.Current_Register_Available_Number+=1;
				emit("\t%_"+this.Current_Register_Available_Number+" = call i8* @calloc(i32 1,i32 "+value+")\n");
				int timh2=this.Current_Register_Available_Number;
				this.Current_Register_Available_Number+=1;
				emit("\t%_"+this.Current_Register_Available_Number+" =  bitcast i8* %_"+timh2+" to i32*\n");
				int ft=this.Current_Register_Available_Number;
				emit("\tstore i32 "+value+" , i32* %_"+this.Current_Register_Available_Number+"\n");
				this.Type_Value="Inside-Boolean";
				this.Current_Register_Available_Number+=1;
				emit("\t%_"+this.Current_Register_Available_Number+" = getelementptr i8, i8* %this, i32 "+valu1+"\n");
				int f1=this.Current_Register_Available_Number;
				this.Current_Register_Available_Number+=1;
				emit("\t%_"+this.Current_Register_Available_Number+" = bitcast i8* %_"+f1+" to "+found+"*\n");
				int f2=this.Current_Register_Available_Number;
				this.Current_Register_Available_Number+=1;
				emit("\tstore i8* %_"+timh2+", i8** %_"+f2+"\n");
			}
		}
		return null;
	}
	
	/**
	* f0 -> "new"
	* f1 -> "int"
	* f2 -> "["
	* f3 -> Expression
	* f4 -> "]"
	*/
	public String visit(IntegerArrayAllocationExpression n,SymbolTable symtable) throws Exception{
		n.f3.accept(this,symtable);
		String id=this.Object_New;
		String found=Class_Member(symtable,id,this.Current_Class);
		if(found==null){
			if(this.Type_Value.equals("Identifier")){
				this.New_Object=false;
				String value=this.Current;
				emit("\t%_"+this.Current_Register_Available_Number+"= add i32 1, "+value);
				emit("\n");
				int timh1=this.Current_Register_Available_Number;
				this.Current_Register_Available_Number+=1;
				emit("\t%_"+this.Current_Register_Available_Number+" = icmp sge i32 %_"+timh1+" , 1");
				emit("\n");
				emit("\tbr i1 %_"+this.Current_Register_Available_Number+",  label %nsz_ok_"+this.val_nsz_ok+", label %nsz_err_"+ this.val_nsz_err);
				emit("\n");
				emit("\tnsz_err_"+this.val_nsz_err+":");
				emit("\n");
				emit("\tcall void @throw_nsz()");
				emit("\n");
				emit("\tbr label %nsz_ok_"+this.val_nsz_ok);
				emit("\n");
				emit("\tnsz_ok_"+this.val_nsz_ok+":");
				emit("\n");
				this.val_nsz_ok+=1;
				this.val_nsz_err+=1;
				this.Current_Register_Available_Number+=1;
				emit("\t%_"+this.Current_Register_Available_Number+" = call i8* @calloc(i32 "+"%_"+timh1+", i32 4)\n");
				int timh2=this.Current_Register_Available_Number;
				this.Current_Register_Available_Number+=1;
				emit("\t%_"+this.Current_Register_Available_Number+" =  bitcast i8* %_"+timh2+" to i32*\n");
				emit("\tstore i32 "+value+" , i32* %_"+this.Current_Register_Available_Number+"\n");
			}
			else{
				this.New_Object=false;
				String value=this.Current;
				emit("\t%_"+this.Current_Register_Available_Number+"= icmp sge i32 "+value+" , 0\n");
				int timh2=this.Current_Register_Available_Number;
				this.Current_Register_Available_Number+=1;
				emit("\tbr i1 %_"+timh2+",  label %nsz_ok_"+this.val_nsz_ok+", label %nsz_err_"+ this.val_nsz_err+"\n");
				emit("\tnsz_err_"+this.val_nsz_err+":");
				emit("\n");
				emit("\tcall void @throw_nsz()");
				emit("\n");
				emit("\tbr label %nsz_ok_"+this.val_nsz_ok);
				emit("\n");
				emit("\tnsz_ok_"+this.val_nsz_ok+":");
				emit("\n");
				emit("\t%_"+this.Current_Register_Available_Number+" = add i32 "+value+", 1\n");
				int timh3=this.Current_Register_Available_Number;
				this.Current_Register_Available_Number+=1;
				emit("\t%_"+this.Current_Register_Available_Number+" = call i8* @calloc(i32 4, i32 %_"+timh3+")\n");
				int timh5=this.Current_Register_Available_Number;
				this.Current_Register_Available_Number+=1;
				emit("\t%_"+this.Current_Register_Available_Number+" = bitcast i8* %_"+timh5+" to i32*\n");
				int timh6=this.Current_Register_Available_Number;
				emit("\tstore i32 "+value+", i32* %_"+timh6+"\n");
				this.val_nsz_ok+=1;
				this.val_nsz_err+=1;
				
			}
		}
		else{
			this.New_Object=true;
			int valu1=position(symtable,id,this.Current_Class);
			if(this.Type_Value.equals("Identifier")){
				String value=this.Current;
				emit("\t%_"+this.Current_Register_Available_Number+"= add i32 1, "+value);
				emit("\n");
				int timh1=this.Current_Register_Available_Number;
				this.Current_Register_Available_Number+=1;
				emit("\t%_"+this.Current_Register_Available_Number+" = icmp sge i32 %_"+timh1+" , 1");
				emit("\n");
				emit("\tbr i1 %_"+this.Current_Register_Available_Number+",  label %nsz_ok_"+this.val_nsz_ok+", label %nsz_err_"+ this.val_nsz_err);
				emit("\n");
				emit("\tnsz_err_"+this.val_nsz_err+":");
				emit("\n");
				emit("\tcall void @throw_oob()");
				emit("\n");
				emit("\tbr label %nsz_ok_"+this.val_nsz_ok);
				emit("\n");
				emit("\tnsz_ok_"+this.val_nsz_ok+":");
				emit("\n");
				this.val_nsz_ok+=1;
				this.val_nsz_err+=1;
				this.Current_Register_Available_Number+=1;
				emit("\t%_"+this.Current_Register_Available_Number+" = call i8* @calloc(i32 "+"%_"+timh1+", i32 4)\n");
				int timh2=this.Current_Register_Available_Number;
				this.Current_Register_Available_Number+=1;
				emit("\t%_"+this.Current_Register_Available_Number+" =  bitcast i8* %_"+timh2+" to i32*\n");
				emit("\tstore i32 "+value+" , i32* %_"+this.Current_Register_Available_Number+"\n");
				int ft=this.Current_Register_Available_Number;
				this.Current_Register_Available_Number+=1;
				emit("\t%_"+this.Current_Register_Available_Number+" = getelementptr i8, i8* %this, i32 "+valu1+"\n");
				int f1=this.Current_Register_Available_Number;
				this.Current_Register_Available_Number+=1;
				emit("\t%_"+this.Current_Register_Available_Number+" = bitcast i8* %_"+f1+" to "+found+"*\n");
				int f2=this.Current_Register_Available_Number;
				this.Current_Register_Available_Number+=1;
				emit("\tstore i32* %_"+ft+", i32** %_"+f2+"\n");
			}
			else{
				this.Type_Value="Inside-Interger";
				String value=this.Current;
				emit("\t%_"+this.Current_Register_Available_Number+"= icmp slt i32 "+value+" , 0\n");
				int timh2=this.Current_Register_Available_Number;
				this.Current_Register_Available_Number+=1;
				emit("\tbr i1 %_"+timh2+",  label %nsz_err_"+this.val_nsz_err+", label %nsz_ok_"+ this.val_nsz_ok+"\n");
				emit("\tnsz_err_"+this.val_nsz_err+":");
				emit("\n");
				emit("\tcall void @throw_oob()");
				emit("\n");
				emit("\tbr label %nsz_ok_"+this.val_nsz_ok);
				emit("\n");
				emit("\tnsz_ok_"+this.val_nsz_ok+":");
				emit("\n");
				emit("\t%_"+this.Current_Register_Available_Number+" = add i32 "+value+", 1\n");
				int timh3=this.Current_Register_Available_Number;
				this.Current_Register_Available_Number+=1;
				emit("\t%_"+this.Current_Register_Available_Number+" = call i8* @calloc(i32 4, i32 %_"+timh3+")\n");
				int timh5=this.Current_Register_Available_Number;
				this.Current_Register_Available_Number+=1;
				emit("\t%_"+this.Current_Register_Available_Number+" = bitcast i8* %_"+timh5+" to i32*\n");
				int timh6=this.Current_Register_Available_Number;
				this.Current_Register_Available_Number+=1;
				emit("\tstore i32 "+value+", i32* %_"+timh6+"\n");
				this.val_nsz_ok+=1;
				this.val_nsz_err+=1;
				emit("\t%_"+this.Current_Register_Available_Number+" = getelementptr i8, i8* %this, i32 "+valu1+"\n");
				int f1=this.Current_Register_Available_Number;
				this.Current_Register_Available_Number+=1;
				emit("\t%_"+this.Current_Register_Available_Number+" = bitcast i8* %_"+f1+" to  "+found+"*\n");
				int f2=this.Current_Register_Available_Number;
				this.Current_Register_Available_Number+=1;
				emit("\tstore i32* %_"+timh6+", i32** %_"+f2+"\n");
			}
		}
		this.Type_Value="Inside-Interger";
		return null;
	}
	/**
	* f0 -> "new"
	* f1 -> Identifier
	* f2 -> "("
	* f3 -> ")"
	*/
	public String visit(AllocationExpression n,SymbolTable symtable) throws Exception{
		this.Type_Value="AllocationExpression";
		n.f1.accept(this,symtable);
		String value=this.Current;
		this.newClass=value;
		int cost_bytes=symtable.Byte_Calculation(symtable,value);
		cost_bytes+=8;
		emit("\t%_"+this.Current_Register_Available_Number+" = call i8* @calloc(i32 1, i32 "+cost_bytes+")\n"); 
		int timh1=this.Current_Register_Available_Number;
		this.Current_Register_Available_Number+=1;
		emit("\t%_"+this.Current_Register_Available_Number+" = bitcast i8* %_"+ timh1+ " to i8***\n");
		int timh2=this.Current_Register_Available_Number;
		this.Current_Register_Available_Number+=1;
		int coun_fun=symtable.Count_Functions(symtable,value);
		emit("\t%_"+this.Current_Register_Available_Number+"= getelementptr ["+coun_fun+" x i8*], ["+coun_fun+" x i8*]* @."+value+"_vtable, i32 0, i32 0\n");
		int timh3=this.Current_Register_Available_Number;
		this.Current_Register_Available_Number+=1;
		emit("\tstore i8** %_"+timh3+", i8*** %_"+timh2+"\n");
		this.Type_Value="Allocation";
		this.Current="%_"+timh1;
		return null;
	}


	/**
	* f0 -> "("
	* f1 -> Expression
	* f2 -> ")"
	*/
	public String visit(BracketExpression n,SymbolTable symtable) throws Exception{
		this.Type_Value="BracketExpression";
		n.f1.accept(this,symtable);
		return null;
	}

	/** 
	* f0 -> AndExpression
		|	CompareExpression
		|	PlusExpression
		|	MinusExpression
		|	TimesExpression
		|	ArrayLookup
		|	ArrayLength
		|	MessageSend
		|	Clause
	*/
	public String visit(Expression n,SymbolTable symtable) throws Exception{
		this.Type_Value="Expression";
		n.f0.accept(this,symtable);
		return null;
	}



	/**
	* f0 -> Clause
	* f1 -> "&&"
	* f2 -> Clause
	*/
	public String visit(AndExpression n,SymbolTable symtable) throws Exception{
		n.f0.accept(this,symtable);
		String id1=this.Current;
		int e=this.expr_res+1;
		int n1=this.expr_res+3;
		int n2=this.expr_res+2;
		emit("\tbr i1 "+id1+", label %exp_res_"+e+", label %exp_res_"+this.expr_res+"\n");
		emit("\texp_res_"+this.expr_res+":\n");
		int t=this.expr_res;
		emit("\tbr label %exp_res_"+n1+"\n");
		emit("\texp_res_"+e+":\n");
		n.f2.accept(this,symtable);
		String id2=this.Current;
		emit("\tbr label %exp_res_"+n2+"\n");
		emit("\texp_res_"+n2+":\n");
		emit("\tbr label %exp_res_"+n1+"\n");
		emit("\texp_res_"+n1+":\n");
		emit("\t%_"+this.Current_Register_Available_Number+" = phi i1  [ 0, %exp_res_"+t+" ], [ "+id2+", %exp_res_"+n2+" ]\n");
		this.expr_res+=8;
		this.Current="%_"+this.Current_Register_Available_Number;
		this.Current_Register_Available_Number+=1;
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
	* f0 -> PrimaryExpression
	* f1 -> "<"
	* f2 -> PrimaryExpression
	*/
	public String visit(CompareExpression n,SymbolTable symtable) throws Exception{
		n.f0.accept(this,symtable);
		String final_type1=this.Current;
		n.f2.accept(this,symtable);
		String final_type2=this.Current;
		emit("\t%_"+this.Current_Register_Available_Number+"= icmp slt i32 "+final_type1+", "+final_type2+"\n");
		this.Current="%_"+this.Current_Register_Available_Number;
		this.Current_Register_Available_Number+=1;
		this.Type_Value="CompareExpression";
		return null;
	}



	/**
	* f0 -> PrimaryExpression
	* f1 -> "+"
	* f2 -> PrimaryExpression
	*/
	public String visit(PlusExpression n,SymbolTable symtable) throws Exception{
		n.f0.accept(this,symtable);
		String final_type1=this.Current;
		n.f2.accept(this,symtable);
		String final_type2=this.Current;
		emit("\t%_"+this.Current_Register_Available_Number+"= add i32 "+final_type1+", "+final_type2+"\n");
		this.Current="%_"+this.Current_Register_Available_Number;
		this.Current_Register_Available_Number+=1;
		this.Type_Value="PlusExpression";
		return null;
	}

	/**
	* f0 -> PrimaryExpression
	* f1 -> "-"
	* f2 -> PrimaryExpression
	*/
	public String visit(MinusExpression n,SymbolTable symtable) throws Exception{
		n.f0.accept(this,symtable);
		String final_type1=this.Current;
		n.f2.accept(this,symtable);
		String final_type2=this.Current;
		emit("\t%_"+this.Current_Register_Available_Number+"= sub i32 "+final_type1+", "+final_type2+"\n");
		this.Current="%_"+this.Current_Register_Available_Number;
		this.Current_Register_Available_Number+=1;
		this.Type_Value="MinusExpression";
		return null;
	}

	

	/**
	* f0 -> PrimaryExpression
	* f1 -> "*"
	* f2 -> PrimaryExpression
	*/
	public String visit(TimesExpression n,SymbolTable symtable) throws Exception{
		n.f0.accept(this,symtable);
		String final_type1=this.Current;
		n.f2.accept(this,symtable);
		String final_type2=this.Current;
		emit("\t%_"+this.Current_Register_Available_Number+"= mul i32 "+final_type1+", "+final_type2+"\n");
		this.Current="%_"+this.Current_Register_Available_Number;
		this.Current_Register_Available_Number+=1;
		this.Type_Value="TimesExpression";
		return null;
	}

	/**
	* f0->  PrimaryExpression
	* f1 -> "["
	* f2 -> PrimaryExpression
	* f3 -> "]"
	*/
	public String visit(ArrayLookup n,SymbolTable symtable) throws Exception{
		n.f0.accept(this,symtable);
		String id1=this.Current;
		String type=this.type_on_arrayassignment;
		n.f2.accept(this,symtable);
		String id2=this.Current;
		String offset=id2;
		if(type.equals("i32*")){
			if(this.this_item==false){
				String val1=id1;
				emit("\t%_"+this.Current_Register_Available_Number+" = load i32, i32* "+val1+"\n");
				int val2=this.Current_Register_Available_Number;
				this.Current_Register_Available_Number+=1;
				emit("\t%_"+this.Current_Register_Available_Number+" = icmp sge i32 "+offset+", 0\n");
				int val3=this.Current_Register_Available_Number;
				this.Current_Register_Available_Number+=1;
				emit("\t%_"+this.Current_Register_Available_Number+" = icmp slt i32 "+offset+", %_"+val2+"\n");
				int val4=this.Current_Register_Available_Number;
				this.Current_Register_Available_Number+=1;
				emit("\t%_"+this.Current_Register_Available_Number+" = and i1 %_"+val3+", %_"+val4+"\n");
				int val5=this.Current_Register_Available_Number;
				this.Current_Register_Available_Number+=1;
				emit("\tbr i1 %_"+val5+", label %oob_ok_"+this.oob_ok+", label %oob_err_"+this.oob_err+"\n");
				emit("\toob_err_"+this.oob_err+":\n");
				emit("\tcall void @throw_oob()\n");
				emit("\tbr label %oob_ok_"+this.oob_ok+"\n");
				emit("\toob_ok_"+this.oob_ok+":\n");
				emit("\t%_"+this.Current_Register_Available_Number+"= add i32 1,"+offset+"\n");
				int val6=this.Current_Register_Available_Number;
				this.Current_Register_Available_Number+=1;
				emit("\t%_"+this.Current_Register_Available_Number+" = getelementptr i32, i32* "+val1+", i32 %_"+val6+"\n");
				int val7=this.Current_Register_Available_Number;
				this.Current_Register_Available_Number+=1;
				emit("\t%_"+this.Current_Register_Available_Number+" = load i32, i32* %_"+val7+"\n");
				this.Current="%_"+this.Current_Register_Available_Number;
				this.Current_Register_Available_Number+=1;
				this.oob_ok+=1;
				this.oob_err+=1;
			}
			else{
				String val1=id1;
				emit("\t%_"+this.Current_Register_Available_Number+" = load i32, i32* "+val1+"\n");
				int val2=this.Current_Register_Available_Number;
				this.Current_Register_Available_Number+=1;
				emit("\t%_"+this.Current_Register_Available_Number+" = icmp sge i32 "+offset+", 0\n");
				int val3=this.Current_Register_Available_Number;
				this.Current_Register_Available_Number+=1;
				emit("\t%_"+this.Current_Register_Available_Number+" = icmp slt i32 "+offset+", %_"+val2+"\n");
				int val4=this.Current_Register_Available_Number;
				this.Current_Register_Available_Number+=1;
				emit("\t%_"+this.Current_Register_Available_Number+" = and i1 %_"+val3+", %_"+val4+"\n");
				int val5=this.Current_Register_Available_Number;
				this.Current_Register_Available_Number+=1;
				emit("\tbr i1 %_"+val5+", label %oob_ok_"+this.oob_ok+", label %oob_err_"+this.oob_err+"\n");
				emit("\toob_err_"+this.oob_err+":\n");
				emit("\tcall void @throw_oob()\n");
				emit("\tbr label %oob_ok_"+this.oob_ok+"\n");
				emit("\toob_ok_"+this.oob_ok+":\n");
				emit("\t%_"+this.Current_Register_Available_Number+"= add i32 1,"+offset+"\n");
				int val6=this.Current_Register_Available_Number;
				this.Current_Register_Available_Number+=1;
				emit("\t%_"+this.Current_Register_Available_Number+" = getelementptr i32, i32* "+val1+", i32 %_"+val6+"\n");
				int val7=this.Current_Register_Available_Number;
				this.Current_Register_Available_Number+=1;
				emit("\t%_"+this.Current_Register_Available_Number+" = load i32, i32* %_"+val7+"\n");
				this.Current="%_"+this.Current_Register_Available_Number;
				this.Current_Register_Available_Number+=1;
				this.oob_ok+=1;
				this.oob_err+=1;
			}
			this.Type_Value="ArrayLookup-Interger";
		}
		else if(type.equals("i8*")){
			if(this.this_item==false){
				String val1=id1;
				emit("\t%_"+this.Current_Register_Available_Number+" = bitcast i8* "+val1+" to i32*\n");
				int val2=this.Current_Register_Available_Number;
				this.Current_Register_Available_Number+=1;
				emit("\t%_"+this.Current_Register_Available_Number+" = load i32, i32* %_"+val2+"\n");
				int val3=this.Current_Register_Available_Number;
				this.Current_Register_Available_Number+=1;
				emit("\t%_"+this.Current_Register_Available_Number+" = icmp sge i32 "+offset+",  0\n");
				int val4=this.Current_Register_Available_Number;
				this.Current_Register_Available_Number+=1;
				emit("\t%_"+this.Current_Register_Available_Number+" = icmp slt i32 "+offset+", %_"+val3+"\n");
				int val5=this.Current_Register_Available_Number;
				this.Current_Register_Available_Number+=1;
				emit("\t%_"+this.Current_Register_Available_Number+" = and i1 %_"+val4+", %_"+val5+"\n");
				int val6=this.Current_Register_Available_Number;
				this.Current_Register_Available_Number+=1;
				emit("\tbr i1 %_"+val6+", label %oob_ok_"+this.oob_ok+", label %oob_err_"+this.oob_err+"\n");
				int val7=this.Current_Register_Available_Number;
				this.Current_Register_Available_Number+=1;
				emit("\toob_err_"+this.oob_err+":\n");
				emit("\tcall void @throw_oob()\n");
				emit("\tbr label %oob_ok_"+this.oob_ok+"\n");
				emit("\toob_ok_"+this.oob_ok+":\n");
				emit("\t%_"+this.Current_Register_Available_Number+" = add i32 4, "+offset+"\n");
				int val8=this.Current_Register_Available_Number;
				this.Current_Register_Available_Number+=1;
				emit("\t%_"+this.Current_Register_Available_Number+" = getelementptr i8, i8* "+val1+", i32 %_"+val8+"\n");
				int val9=this.Current_Register_Available_Number;
				this.Current_Register_Available_Number+=1;
				emit("\t%_"+this.Current_Register_Available_Number+" = load i8, i8* %_"+val9+"\n");
				int val10=this.Current_Register_Available_Number;
				this.Current_Register_Available_Number+=1;
				emit("\t%_"+this.Current_Register_Available_Number+" = trunc i8 %_"+val10+" to i1\n");
				this.Current="%_"+this.Current_Register_Available_Number;
				this.Current_Register_Available_Number+=1;
				this.oob_ok+=1;
				this.oob_err+=1;
			}
			else{
				String val1=this.Current;
				emit("\t%_"+this.Current_Register_Available_Number+"  = load i32*, i32** %_"+val1+"\n");
				int f1=this.Current_Register_Available_Number;
				this.Current_Register_Available_Number+=1;
				n.f2.accept(this,symtable);
				String size=this.Current;
				emit("\t%_"+this.Current_Register_Available_Number+"= load i32, i32 *%_"+f1+"\n");
				int f2=this.Current_Register_Available_Number;
				this.Current_Register_Available_Number+=1;
				emit("\t%_"+this.Current_Register_Available_Number+"  = icmp ult i32 "+size+" , %_"+f2+"\n");
				int start1=this.oob+1;
				int start2=this.oob+2;
				int start3=this.oob+3;
				emit("\tbr i1 %_"+this.Current_Register_Available_Number+" , label %oob"+start1+" , label %oob"+start2+"\n");
				int f3=this.Current_Register_Available_Number;
				this.Current_Register_Available_Number+=1;
				emit("\toob"+start1+":\n");
				emit("\t%_"+this.Current_Register_Available_Number+"  = add i32 "+size+", 1\n");
				int f4=this.Current_Register_Available_Number;
				this.Current_Register_Available_Number+=1;
				emit("\t%_"+this.Current_Register_Available_Number+" = getelementptr i8, i8* %_"+f1+" , i32 %_"+f4+"\n");
				int f5=this.Current_Register_Available_Number;
				this.Current_Register_Available_Number+=1;
				emit("\t%_"+this.Current_Register_Available_Number+"  = load i8, i8* %_"+f5+"\n");
				this.Current="%_"+this.Current_Register_Available_Number;
				this.Current_Register_Available_Number+=1;
				emit("\tbr label %oob"+start3+"\n");	
				emit("\toob"+start2+":\n");
				emit("\tcall void @throw_oob()\n");
				emit("\tbr label %oob"+start3+"\n");
				emit("\toob"+start3+":\n");
			}
			this.Type_Value="ArrayLookup-Boolean";
		}
		return null;
	}


	/**
	* f0 -> PrimaryExpression
	* f1 -> "."
	* f2 -> "length"
	*/
	public String visit(ArrayLength	n,SymbolTable symtable) throws Exception{
		this.Type_Value="ArrayLength";
		return null;
	}


	/**
	* f0-> "!"
	* f1 -> Clause
	*/
	public String visit(NotExpression n,SymbolTable symtable ) throws Exception{
		n.f1.accept(this,symtable);
		String i=this.Current;
		emit("\t%_"+this.Current_Register_Available_Number+"  = xor i1 1, "+i+"\n");
		this.Current="%_"+this.Current_Register_Available_Number;
		this.Current_Register_Available_Number+=1;
		return null;
	}

	/** 
	* f0 -> PrimaryExpression
	* f1 -> "."
	* f2 -> Identifier
	* f3 -> "("
	* f4 ->  ( ExpressionList )?
	* f5 -> ")"
	*/
	public String visit(MessageSend n,SymbolTable symtable) throws Exception{
		n.f0.accept(this,symtable);
		String id=this.Current;
		String type=this.Type_Value;
		boolean exp=false;
		String u=null;
		boolean l=false;
		String search_Class=null;
		if(type.equals("Allocation")){/*new Class()*/
			u=this.Current;
			exp=true;
			search_Class=this.newClass;
		}
		else if(type.equals("ThisExpression")){/*This*/
			u="%this";
			exp=true;
			search_Class=this.Current_Class;
		}
		else if(type.equals("Variable")){/*Variable*/
			u=this.Current;
			search_Class=this.prim;
			this.prim=null;
		}
		else
			l=true;
		if(l==true){
			exp=true;
			search_Class=this.State_re;
			u=this.Current;/*Previous Value for Message Send or another*/
		}
		emit("\t%_"+this.Current_Register_Available_Number+"= bitcast i8* "+u+" to i8***\n");
		int f1=this.Current_Register_Available_Number;
		this.Current_Register_Available_Number+=1;
		emit("\t%_"+this.Current_Register_Available_Number+" = load i8**, i8*** %_"+f1+"\n");
		int f2=this.Current_Register_Available_Number;
		this.Current_Register_Available_Number+=1;
		this.Type_Value="MessageSend";
		n.f2.accept(this,symtable);
		String id1=this.Current;
		String c=null;
		if(exp==false)
			c=symtable.Search_Indentifier(symtable,search_Class,this.Current_Class,this.Name_Fun);
		else
			c=search_Class;
		int positionfun=position_Function(symtable,id1,c);
		emit("\t%_"+this.Current_Register_Available_Number+"= getelementptr i8*, i8** %_"+f2+", i32 "+positionfun+"\n");
		int f3=this.Current_Register_Available_Number;
		this.Current_Register_Available_Number+=1;
		emit("\t%_"+this.Current_Register_Available_Number+" = load i8*, i8** %_"+f3+"\n");
		int f4=this.Current_Register_Available_Number;
		this.Current_Register_Available_Number+=1;
		emit("\t%_"+this.Current_Register_Available_Number+" = bitcast i8* %_"+f4+" to ");
		int f5=this.Current_Register_Available_Number;
		this.Current_Register_Available_Number+=1;
		String re=symtable.Call_Fun(symtable,c,id1,this.FileName,this);
		n.f4.accept(this,symtable);
		emit("\t%_"+this.Current_Register_Available_Number+" = call "+re+" %_"+f5+" (i8* "+u+this.Argu);
		emit(")\n");
		this.Argu="";
		this.Current="%_"+this.Current_Register_Available_Number;
		this.Current_Register_Available_Number+=1;
		this.Type_Value="MessageSend-"+re;
		return null;
	}
	/**
	* f0 -> Expression
	* f1 -> ExpressionTail
	*/
	public String visit(ExpressionList n,SymbolTable symtable) throws Exception{
		n.f0.accept(this,symtable);
		this.Argu+=",";
		if(this.Type_Value.equals("AndExpression"))
			this.Argu+="i1 "+this.Current;
		else if(this.Type_Value.equals("CompareExpression"))
			this.Argu+="i1 "+this.Current;
		else if(this.Type_Value.equals("PlusExpression"))
			this.Argu+="i32 "+this.Current;
		else if(this.Type_Value.equals("MinusExpression"))
			this.Argu+="i32 "+this.Current;
		else if(this.Type_Value.equals("TimesExpression"))
			this.Argu+="i32 "+this.Current;
		else if(this.Type_Value.equals("ArrayLength"))
			this.Argu+="i32 "+this.Current;
		else if(this.Type_Value.equals("ArrayLookup-Boolean"))
			this.Argu+="i1 "+this.Current;
		else if(this.Type_Value.equals("Allocation"))
			this.Argu+="i8* "+this.Current;
		else if(this.Type_Value.equals("ArrayLookup-Interger"))
			this.Argu+="i32 "+this.Current;
		else if(this.Type_Value.equals("MessageSend-i32"))
			this.Argu+="i32 "+this.Current;
		else if(this.Type_Value.equals("MessageSend-i32*"))
			this.Argu+="i32 "+this.Current;
		else if(this.Type_Value.equals("MessageSend-i32*"))
			this.Argu+="i32* "+this.Current;
		else if(this.Type_Value.equals("MessageSend-i1"))
			this.Argu+="i1 "+this.Current;
		else if(this.Type_Value.equals("ThisExpression"))
			this.Argu+="i8* %this";
		else if(this.Type_Value.equals("MessageSend-i8*"))
			this.Argu+="i8* "+this.Current;
		else if(this.Type_Value.equals("Variable"))
			this.Argu+=this.type_on_arrayassignment+"  "+this.Current;
		else if(this.Type_Value.equals("boolean"))
			this.Argu+="i1 "+this.Current;
		else if(this.Type_Value.equals("Identifier"))
			this.Argu+="i32 "+this.Current;
		n.f1.accept(this,symtable);
		return null;
	}


	/**
	* f0 -> (ExpressionTerm)*
	*/
	public String visit(ExpressionTail n,SymbolTable symtable) throws Exception{
		n.f0.accept(this,symtable);
		return null;
	}

	
	
	/**
	* f0 -> ","
	* f1 -> Expression
	*/
	public String visit(ExpressionTerm n,SymbolTable symtable) throws Exception{
		this.Argu+=",";
		n.f1.accept(this,symtable);
		if(this.Type_Value.equals("AndExpression"))
			this.Argu+="i1 "+this.Current;
		else if(this.Type_Value.equals("CompareExpression"))
			this.Argu+="i1 "+this.Current;
		else if(this.Type_Value.equals("Allocation"))
			this.Argu+="i8* "+this.Current;
		else if(this.Type_Value.equals("PlusExpression"))
			this.Argu+="i32 "+this.Current;
		else if(this.Type_Value.equals("MinusExpression"))
			this.Argu+="i32 "+this.Current;
		else if(this.Type_Value.equals("TimesExpression"))
			this.Argu+="i32 "+this.Current;
		else if(this.Type_Value.equals("ArrayLength"))
			this.Argu+="i32 "+this.Current;
		else if(this.Type_Value.equals("ArrayLookup-Boolean"))
			this.Argu+="i1 "+this.Current;
		else if(this.Type_Value.equals("ArrayLookup-Interger"))
			this.Argu+="i32 "+this.Current;
		else if(this.Type_Value.equals("MessageSend-i32"))
			this.Argu+="i32 "+this.Current;
		else if(this.Type_Value.equals("MessageSend-i32*"))
			this.Argu+="i32 "+this.Current;
		else if(this.Type_Value.equals("MessageSend-i32*"))
			this.Argu+="i32* "+this.Current;
		else if(this.Type_Value.equals("MessageSend-i1"))
			this.Argu+="i1 "+this.Current;
		else if(this.Type_Value.equals("MessageSend-i8*"))
			this.Argu+="i8* "+this.Current;
		else if(this.Type_Value.equals("Variable"))
			this.Argu+=this.type_on_arrayassignment+"  "+this.Current;
		else if(this.Type_Value.equals("boolean"))
			this.Argu+="i1 "+this.Current;
		else if(this.Type_Value.equals("Identifier"))
			this.Argu+="i32 "+this.Current;
		else if(this.Type_Value.equals("ThisExpression"))
			this.Argu+="i8* %this";
		return null;
	}





	/**
	* f0-> "this"
	*/
	public String visit(ThisExpression n,SymbolTable symtable) throws Exception{ 
		this.Type_Value="ThisExpression";
		return "this";
	}

	/** 
	* f0 -> "true"
	*/
	public String visit(TrueLiteral n,SymbolTable symtable) throws Exception{ 
		this.Type_Value="boolean";
		this.Current="1";
		return null;
	}



	/** 
	* f0 -> "false"
	*/
	public String visit(FalseLiteral n,SymbolTable symtable) throws Exception{ 
		this.Type_Value="boolean";
		this.Current="0";
		return null;
	}


	/**
    *f0 -> Identifier()
    */
    public String visit(Identifier n,SymbolTable symtable) throws Exception{ 
    	this.Current=n.f0.toString();
    	/*Do Nothing to this Statements*/
    	if(this.Type_Value.equals("VarDeclaration")||this.Type_Value.equals("MainClass")||this.Type_Value.equals("ClassDeclaration")||this.Type_Value.equals("MethodDeclaration")||this.Type_Value.equals("ClassExtendsDeclaration")||this.Type_Value.equals("AllocationExpression")||this.Type_Value.equals("AssignmentStatement")||this.Type_Value.equals("MessageSend"))
    		return this.Current;
    	/*Check Value here*/
    	this.prim=this.Current;
    	String found=Class_Member(symtable,this.Current,this.Current_Class);
    	if(found==null){
    		this.this_item=false;
    		String e=symtable.Value_Type(symtable,this.Current,this.Current_Class,this.Name_Fun);
    		if(e.equals("i32")){
    			emit("\t%_"+this.Current_Register_Available_Number+" = load i32, i32* %"+this.Current+"\n");
    			this.Current="%_"+this.Current_Register_Available_Number;
    			this.type_on_arrayassignment="i32";
    			this.Current_Register_Available_Number+=1;
    		}
    		else if(e.equals("i32*")){
    			emit("\t%_"+this.Current_Register_Available_Number+" = load i32*, i32** %"+this.Current+"\n");
    			this.Current="%_"+this.Current_Register_Available_Number;
    			this.type_on_arrayassignment="i32*";
    			this.Current_Register_Available_Number+=1;
    		}
    		else if(e.equals("i1")){
    			emit("\t%_"+this.Current_Register_Available_Number+" = load i1, i1* %"+this.Current+"\n");
    			this.Current="%_"+this.Current_Register_Available_Number;
    			this.type_on_arrayassignment="i1";
    			this.Current_Register_Available_Number+=1;
    		}
    		else{
    			emit("\t%_"+this.Current_Register_Available_Number+" = load i8*, i8** %"+this.Current+"\n");
    			this.Current="%_"+this.Current_Register_Available_Number;
    			this.type_on_arrayassignment="i8*";
    			this.Current_Register_Available_Number+=1;
    		}
    	}
    	else{
    		this.this_item=true;
    		int valu1=position(symtable,this.Current,this.Current_Class);
    		this.type_on_arrayassignment=found;
			emit("\t%_"+this.Current_Register_Available_Number+" = getelementptr i8, i8* %this, i32 "+valu1+"\n");
			int f1=this.Current_Register_Available_Number;
			this.Current_Register_Available_Number+=1;
			emit("\t%_"+this.Current_Register_Available_Number+" = bitcast i8* %_"+f1+" to "+found+"*\n");
			int f2=this.Current_Register_Available_Number;
			this.Current_Register_Available_Number+=1;
			if(this.re==false){
				if(this.Place==true){
					emit("\t%_"+this.Current_Register_Available_Number+" = load "+found+", "+found+"* %_"+f2+"\n");
					this.Current="%_"+this.Current_Register_Available_Number;
					this.Current_Register_Available_Number+=1;
				}
				else{
					this.Current="%_"+this.Current_Register_Available_Number;
					this.Current_Register_Available_Number+=1;
				}
			}
			else{
				emit("\t%_"+this.Current_Register_Available_Number+" = load "+found+", "+found+"* %_"+f2+"\n");
				this.Current="%_"+this.Current_Register_Available_Number;
				this.Current_Register_Available_Number+=1;
			}
    	}
    	this.Type_Value="Variable";
		return n.f0.toString();
    }
     /**
     * f0 -> INTEGER_LITERAL
     */
    public String visit(IntegerLiteral n,SymbolTable symtable) throws Exception {
    	this.Current=n.f0.toString();
    	this.Type_Value="Identifier";
		return null;
	}


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
       	/*Store all parameters of Function here*/
      	if(type.equals("int")){
      		emit("\t%"+ide+"= alloca i32\n");
      		emit("\tstore i32 %."+ide+", i32* %"+ide+"\n");
      	}
      	else if(type.equals("int[]")){
      		emit("\t%"+ide+"= alloca i32*\n");
      		emit("\tstore i32* %."+ide+", i32** %"+ide+"\n");
      	}
      	else if(type.equals("boolean")){
      		emit("\t%"+ide+"= alloca i1\n");
      		emit("\tstore i1 %."+ide+", i1* %"+ide+"\n");
      	}
      	else{
      		emit("\t%"+ide+"= alloca i8*\n");
      		emit("\tstore i8* %."+ide+", i8** %"+ide+"\n");
      	}
        return null;
    }

}

