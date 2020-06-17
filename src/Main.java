import syntaxtree.*;
import java.util.Map;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.HashMap;
import java.io.*;


class Main {
    public static void main (String[] args) throws Exception{
		if(args.length==0){
		    System.err.println("Usage: java Driver [file1] [file2] ... [fileN]");
		    System.exit(1);
		}
		FileInputStream fis = null;
		try{
			for(int i=0;i<args.length;i++){
			    fis = new FileInputStream(args[i]);
			    MiniJavaParser parser = new MiniJavaParser(fis);
			    Goal root = parser.Goal();
			    FirstVisitor firstvisitor=new FirstVisitor();
			    SymbolTable symboltable=new SymbolTable();
			    MiniJavatoLLVM node =new MiniJavatoLLVM();
			    //Vtable vtable=new Vtable();
			    System.out.println("Program parsed successfully.");
				try{
					root.accept(firstvisitor,symboltable);/*Save Class Names,Fields, Methods and Prototype of each Method*/
					symboltable.Calculate_Vtable(symboltable);/*Create V_Table*/
					symboltable.printval(symboltable,firstvisitor);/*Emit Vtable of Classes*/
					root.accept(node,symboltable);/*Emit All Other Data*/
				}
				catch(ParseException ex){
					System.out.println(ex.getMessage());
				}
			}
		}
		catch(ParseException ex){
		    System.out.println(ex.getMessage());
		}
		catch(FileNotFoundException ex){
		    System.err.println(ex.getMessage());
		}
		finally{
		    try{
			if(fis != null) fis.close();
		    }
		    catch(IOException ex){
			System.err.println(ex.getMessage());
		    }
		}
    }
}
