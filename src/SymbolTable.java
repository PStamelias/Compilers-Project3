import java.io.*;
import java.util.Map;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.HashMap;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
public  class SymbolTable {
	public   LinkedHashMap<String,ClassInfo> My_map;
    public LinkedHashMap<String,Info> Vmap;/*V_Table*/
    public LinkedHashMap<String,VarMap> Decl;/*Declaration Hash Map*/
	SymbolTable(){
		My_map=new  LinkedHashMap<String,ClassInfo>();
        Vmap=new  LinkedHashMap<String,Info>();
        Decl= new  LinkedHashMap<String,VarMap>();
	}
    public static class  ClassInfo{
    	public String parent_Class;
        public String Name;
    	public boolean Main_Class;
    	public LinkedHashMap<String,String> Field_map;
    	public LinkedHashMap<String,MethodInfo> Method_map;
    	ClassInfo(){
    		this.parent_Class=null;
    		this.Main_Class=false;
            this.Name=null;
    		this.Field_map=new LinkedHashMap<String,String>();
    		this.Method_map= new LinkedHashMap<String,MethodInfo>();
    	}
    }
    public static  class VarMap{
        public String name;
        public LinkedHashMap<String,String> variable;
        VarMap(){
            this.name=null;
            this.variable=new LinkedHashMap<String,String>();
        }
    }
    public static class MethodInfo{
        public String name;
        public String return_type;
        public boolean overriding;
        public LinkedHashMap<String,String> parameters;
        MethodInfo(){
            this.name=null;
            this.return_type=null;
            this.overriding=false;
            this.parameters=new LinkedHashMap<String,String>();
        }
    }
    public static class  Info{
        public String parent_Class;
        public String Name;
        public LinkedHashMap<String,Integer> variable;
        public LinkedHashMap<String,Integer> Method_map;
        Info(){
            this.parent_Class=null;
            this.Name=null;
            this.variable=new LinkedHashMap<String,Integer>();
            this.Method_map= new LinkedHashMap<String,Integer>();
        }
    }
    
    public void Calculate_Vtable(SymbolTable sym){/*Create V_Table*/
        for (Map.Entry<String, ClassInfo> entry : My_map.entrySet()) {
            int var_off=0;
            int function_off=0;
            String class_name=entry.getKey();
            SymbolTable.ClassInfo my_class =My_map.get(class_name);
            Vmap.put(class_name,new Info());
            Info a=Vmap.get(class_name);
            a.Name=class_name;
            a.parent_Class=my_class.parent_Class;
            boolean ext=(a.parent_Class==null) ? false : true ;
            if(ext==true){
                ArrayList<String> myList = new ArrayList<String>();
                SymbolTable.ClassInfo r =My_map.get(a.parent_Class);
                while(true){
                    myList.add(r.Name);
                    if(r.parent_Class==null)
                        break;
                    r =My_map.get(r.parent_Class);
                }
                Collections.reverse(myList);
                for (String num : myList){               
                    SymbolTable.ClassInfo x =My_map.get(num);
                    for(Map.Entry<String, String> e : x.Field_map.entrySet()){
                        String name=e.getKey();
                        String type=e.getValue();
                        if(type.equals("int")){
                            a.variable.put(name,var_off);
                            var_off+=4;
                        }
                        else if(type.equals("boolean")){
                            a.variable.put(name,var_off);
                            var_off+=1;
                        }
                        else{
                            a.variable.put(name,var_off);
                            var_off+=8;
                        }
                    }
                    for(Map.Entry<String, MethodInfo> t : x.Method_map.entrySet()){
                        String cl_name=t.getKey();
                        if(a.Method_map.containsKey(cl_name))
                            continue;
                        a.Method_map.put(cl_name,function_off);
                        function_off+=8;
                    }
                }
            }
            SymbolTable.ClassInfo ob =My_map.get(class_name);
            for(Map.Entry<String, String> e : ob.Field_map.entrySet()){
                String name=e.getKey();
                String type=e.getValue();
                if(type.equals("int")){
                    a.variable.put(name,var_off);
                    var_off+=4;
                }
                else if(type.equals("boolean")){
                    a.variable.put(name,var_off);
                    var_off+=1;
                }
                else{
                    a.variable.put(name,var_off);
                    var_off+=8;
                }
            }
            for(Map.Entry<String, MethodInfo> e : ob.Method_map.entrySet()){
                String cl_name=e.getKey();
                if(a.Method_map.containsKey(cl_name))
                    continue;
                a.Method_map.put(cl_name,function_off);
                function_off+=8;
            }
        }   
    }
    public String Search_Indentifier(SymbolTable sym,String var_name,String class_name,String fun_name){/*Searching the type of variable*/
        SymbolTable.VarMap ko=Decl.get(class_name);
        if(ko==null)
            return null;
        for(Map.Entry<String, String> e : ko.variable.entrySet()){
            String type=e.getValue();
            String id=e.getKey();
            if(id.equals(var_name))
                return type;
        }
        SymbolTable.ClassInfo q=My_map.get(class_name);
        SymbolTable.MethodInfo a=q.Method_map.get(fun_name);
        for(Map.Entry<String, String> e :a.parameters.entrySet()){
            String type=e.getValue();
            String id=e.getKey();
            if(id.equals(var_name))
                return type;
        }
        while(true){
            q=My_map.get(class_name);
            for(Map.Entry<String, String> e : q.Field_map.entrySet()){
                String type=e.getValue();
                String id=e.getKey();
                if(id.equals(var_name))
                    return type;
            }
            class_name=q.parent_Class;
            if(class_name==null)
                break;
        }
        return null;   
    }
    public String Call_Fun(SymbolTable sym,String class_identifier,String fun_name,String file,MiniJavatoLLVM m) throws Exception{
        SymbolTable.ClassInfo q=My_map.get(class_identifier);
        SymbolTable.MethodInfo f=null;
        while(true){
            q=My_map.get(class_identifier);
            for(Map.Entry<String, MethodInfo> e : q.Method_map.entrySet()){
                String var=e.getKey();
                if(var.equals(fun_name)){
                    f=e.getValue();
                    break;
                }
            }
            class_identifier=q.parent_Class;
            if(class_identifier==null)
                break;
        }
        String e=null;
        if(f.return_type.equals("int")){
            e="i32";
            emit("i32 ",file);
        }
        else if(f.return_type.equals("int[]")){
            e="i32*";
            emit("i32*",file);
        }
        else if(f.return_type.equals("boolean")){
            e="i1";
            emit("i1",file);
        }
        else{
            e="i8*";
            emit("i8*",file);
        }
        m.State_re=f.return_type;
        emit("(i8*",file);
        for(Map.Entry<String, String> h : f.parameters.entrySet()){
            String e1=h.getValue();
            if(e1.equals("int"))
                emit(",i32",file);
            else if(e1.equals("int[]"))
                emit(",i32*",file);
            else if(e1.equals("boolean"))
                emit(",i1",file);
            else
                emit(",i8*",file);
        }
        emit(")*\n",file);
        return e;
    }
    public String Value_Type(SymbolTable sym,String var_name,String class_name,String fun_name){
        String beg=class_name;
        SymbolTable.VarMap ko=Decl.get(class_name);
        if(ko==null)
            return null;
        for(Map.Entry<String, String> e : ko.variable.entrySet()){
            String type=e.getValue();
            String id=e.getKey();
            if(id.equals(var_name)){
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
        SymbolTable.ClassInfo q=My_map.get(class_name);
        SymbolTable.MethodInfo a=q.Method_map.get(fun_name);
        for(Map.Entry<String, String> e :a.parameters.entrySet()){
            String type=e.getValue();
            String id=e.getKey();
            if(id.equals(var_name)){
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
        while(true){
            q=My_map.get(class_name);
            for(Map.Entry<String, String> e : q.Field_map.entrySet()){
                String type=e.getValue();
                String id=e.getKey();
                if(id.equals(var_name)){
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
            class_name=q.parent_Class;
            if(class_name==null)
                break;
        }
        if(var_name.equals(beg))
            return "i8*";
        if(sym.My_map.containsKey(beg))
            return "i8*";
        return null;
    }
    public void emit(String message,String file) throws Exception{/*Emit*/
        PrintWriter pw=new PrintWriter(new FileOutputStream(new File(file+".ll"),true));
        if(pw==null)
            throw new Exception("Error:PrintWriter");
        pw.append(message);
        pw.close();
    }
    public int Byte_Calculation(SymbolTable sym,String class_name) throws Exception{
        int sum=0;
        SymbolTable.ClassInfo my_class =My_map.get(class_name);
        ArrayList<String> myList = new ArrayList<String>();
        SymbolTable.ClassInfo r =My_map.get(my_class.parent_Class);
        if(r==null){
            for(Map.Entry<String, String> e : my_class.Field_map.entrySet()){
                String type=e.getValue();
                if(type.equals("int"))
                    sum+=4;
                else if(type.equals("boolean"))
                    sum+=1;
                else 
                    sum+=8;
            }
            return sum;
        }
        while(true){
            if(r==null)
                break;
            myList.add(r.Name);
            r =My_map.get(r.parent_Class);
        }
        Collections.reverse(myList);
        myList.add(class_name);
        for (String num : myList){               
            SymbolTable.ClassInfo x =My_map.get(num);
            for(Map.Entry<String, String> e : x.Field_map.entrySet()){
                String type=e.getValue();
                if(type.equals("int"))
                    sum+=4;
                else if(type.equals("boolean"))
                    sum+=1;
                else 
                    sum+=8;
            }
        }
        return sum;
    }
    public int Count_Functions(SymbolTable sym,String class_name){/*Return the number of each Function */
        SymbolTable.Info my_class =Vmap.get(class_name);
        int sum=0;
        for (Map.Entry<String,Integer> entry : my_class.Method_map.entrySet())
            sum+=1; 
        return sum;
    }
    public void printval(SymbolTable sym,FirstVisitor first) throws Exception{/*Emit Class Data of each class (plus Main Class)*/
        for (Map.Entry<String,Info> entry : Vmap.entrySet()){
            String class_name=entry.getKey();
            String beg=class_name;
            Info node =Vmap.get(class_name);
            emit("@."+class_name+"_vtable= global [",first.FileName);
            int counter=0;
            for(Map.Entry<String, Integer> e : node.Method_map.entrySet())
                counter+=1;
            emit(counter+" x i8*][\n",first.FileName);
            int val=0;
            SymbolTable.ClassInfo ob =My_map.get(beg);
            for(Map.Entry<String, Integer> e : node.Method_map.entrySet()){
                val+=1;
                emit("\ti8* bitcast ",first.FileName);
                String g=e.getKey();
                String return_value=null;
                ob =My_map.get(beg);
                SymbolTable.MethodInfo p =ob.Method_map.get(g);
                class_name=beg;
                if(p==null){
                    while(true){
                        class_name=ob.parent_Class;
                        ob =My_map.get(ob.parent_Class);
                        p =ob.Method_map.get(g);
                        if(p!=null)
                            break;
                    }
                }
                return_value=p.return_type;
                if(return_value.equals("int")){
                    emit("(i32 ",first.FileName);
                    int coun=0;
                    int u;
                    for(Map.Entry<String,String>  k : p.parameters.entrySet())
                        coun+=1;
                    if(coun==0)
                        emit("(i8*)*",first.FileName);
                    else{
                        u=0;
                        emit("(i8*,",first.FileName);
                        for(Map.Entry<String,String>  k : p.parameters.entrySet()){
                            String type=k.getValue();
                            if(type.equals("int"))
                                emit("i32",first.FileName);
                            else if(type.equals("boolean"))
                                emit("i1",first.FileName);
                            else if(type.equals("int[]"))
                                emit("i32*",first.FileName);
                            else if(type.equals("boolean[]"))
                                emit("i8*",first.FileName);
                            else
                                emit("i8*",first.FileName);
                            u+=1;
                            if(u!=coun)
                                emit(",",first.FileName);
                        }
                        emit(")*",first.FileName);
                    }
                    if(val==counter)
                        emit(" @"+class_name+"."+g+" to i8*)\n",first.FileName);
                    else
                        emit(" @"+class_name+"."+g+" to i8*),\n",first.FileName);
                }
                else if(return_value.equals("boolean")){
                    emit("(i1 ",first.FileName);
                    int coun=0;
                    int u;
                    for(Map.Entry<String,String>  k : p.parameters.entrySet())
                        coun+=1;
                    if(coun==0)
                        emit("(i8*)*",first.FileName);
                    else{
                        u=0;
                        emit("(i8*,",first.FileName);
                        for(Map.Entry<String,String>  k : p.parameters.entrySet()){
                            String type=k.getValue();
                            if(type.equals("int"))
                                emit("i32",first.FileName);
                            else if(type.equals("boolean"))
                                emit("i1",first.FileName);
                            else if(type.equals("int[]"))
                                emit("i32*",first.FileName);
                            else if(type.equals("boolean[]"))
                                emit("i8*",first.FileName);
                            else
                                emit("i8*",first.FileName);
                            u+=1;
                            if(u!=coun)
                                emit(",",first.FileName);
                        }
                        emit(")*",first.FileName);
                    }
                    if(val==counter)
                        emit(" @"+class_name+"."+g+" to i8*)\n",first.FileName);
                    else
                        emit(" @"+class_name+"."+g+" to i8*),\n",first.FileName);
                }
                else if(return_value.equals("int[]")){
                    emit("(i32* ",first.FileName);
                    int coun=0;
                    int u;
                    for(Map.Entry<String,String>  k : p.parameters.entrySet())
                        coun+=1;
                    if(coun==0)
                        emit("(i8*)*",first.FileName);
                    else{
                        u=0;
                        emit("(i8*,",first.FileName);
                        for(Map.Entry<String,String>  k : p.parameters.entrySet()){
                            String type=k.getValue();
                            if(type.equals("int"))
                                emit("i32",first.FileName);
                            else if(type.equals("boolean"))
                                emit("i1",first.FileName);
                            else if(type.equals("int[]"))
                                emit("i32*",first.FileName);
                            else if(type.equals("boolean[]"))
                                emit("i8*",first.FileName);
                            else
                                emit("i8*",first.FileName);
                            u+=1;
                            if(u!=coun)
                                emit(",",first.FileName);
                        }
                        emit(")*",first.FileName);
                    }
                    if(val==counter)
                        emit(" @"+class_name+"."+g+" to i8*)\n",first.FileName);
                    else
                        emit(" @"+class_name+"."+g+" to i8*),\n",first.FileName);
                }
                else if(return_value.equals("boolean[]")){
                    emit("(i8* ",first.FileName);
                    int coun=0;
                    int u;
                    for(Map.Entry<String,String>  k : p.parameters.entrySet())
                        coun+=1;
                    if(coun==0)
                        emit("(i8*)*",first.FileName);
                    else{
                        u=0;
                        emit("(i8*,",first.FileName);
                        for(Map.Entry<String,String>  k : p.parameters.entrySet()){
                            String type=k.getValue();
                            if(type.equals("int"))
                                emit("i32",first.FileName);
                            else if(type.equals("boolean"))
                                emit("i1",first.FileName);
                            else if(type.equals("int[]"))
                                emit("i32*",first.FileName);
                            else if(type.equals("boolean[]"))
                                emit("i8*",first.FileName);
                            else
                                emit("i8*",first.FileName);
                            u+=1;
                            if(u!=coun)
                                emit(",",first.FileName);
                        }
                        emit(")*",first.FileName);
                    }
                    if(val==counter)
                        emit(" @"+class_name+"."+g+" to i8*)\n",first.FileName);
                    else
                        emit(" @"+class_name+"."+g+" to i8*),\n",first.FileName);
                }
                else {
                    emit("(i8* ",first.FileName);
                    int coun=0;
                    int u;
                    for(Map.Entry<String,String>  k : p.parameters.entrySet())
                        coun+=1;
                    if(coun==0)
                        emit("(i8*)*",first.FileName);
                    else{
                        u=0;
                        emit("(i8*,",first.FileName);
                        for(Map.Entry<String,String>  k : p.parameters.entrySet()){
                            String type=k.getValue();
                            if(type.equals("int"))
                                emit("i32",first.FileName);
                            else if(type.equals("boolean"))
                                emit("i1",first.FileName);
                            else if(type.equals("int[]"))
                                emit("i32*",first.FileName);
                            else if(type.equals("boolean[]"))
                                emit("i8*",first.FileName);
                            else
                                emit("i8*",first.FileName);
                            u+=1;
                            if(u!=coun)
                                emit(",",first.FileName);
                        }
                        emit(")*",first.FileName);
                    }
                    if(val==counter)
                        emit(" @"+class_name+"."+g+" to i8*)\n",first.FileName);
                    else
                        emit(" @"+class_name+"."+g+" to i8*),\n",first.FileName);
                }
            }
            emit("]\n\n",first.FileName);
        }
    }
}
