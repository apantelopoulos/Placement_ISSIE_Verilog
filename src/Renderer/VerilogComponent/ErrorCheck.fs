module ErrorCheck

open VerilogTypes
open Fable.Core.JsInterop



/// Checks whether all ports given in the beginning of the module are defined as input/output
let portCheck ast portMap errorList = 
    let portList = ast.Module.PortList |> Array.toList
    printfn "Ports: %A" portList
    let items = ast.Module.ModuleItems.ItemList |> Array.toList
    let decls = 
        items |> List.collect (fun x -> 
            match (x.IODecl |> isNullOrUndefined) with
            | false -> 
                match x.IODecl with
                | Some d -> 
                    d.Variables 
                    |> Array.toList 
                    |> List.collect (fun x -> [x.Name]) 
                | None -> []
            | true -> []
        ) 
    let diff = Seq.except (decls |> List.toSeq) (portList |> List.toSeq)
    if Seq.isEmpty diff then 
        printfn "All ports are declared either as input or output"
    else 
        printfn"Undeclared ports: %A" diff


    match Seq.isEmpty diff with
    | false -> List.append errorList [sprintf "The following ports are not declared either as input or output: %A" diff]
    | true -> errorList

/// Checks if the name of the module is valid (i.e. starts with a character)
let nameCheck ast errorList = 
    let name =  ast.Module.ModuleName.Name
    printfn "Name of module: %s" ast.Module.ModuleName.Name
    let notGoodName =
        name
        |> Seq.toList
        |> List.tryHead
        |> function | Some ch when  System.Char.IsLetter ch -> false | _ -> true

    match notGoodName with
    | true -> List.append errorList [sprintf "Module Name must start with a character to be valid"]
    | false -> errorList

/// Checks the names used for parameters
/// Throws an error if the name is used for a port 
let parameterNameCheck ast parameterNames portMap errorList = 
    let localErrors = 
        List.collect (fun name -> 
            match Map.tryFind name portMap with
            | Some found -> [sprintf "Variable %s cannot be used as a parameter name because it is declared as a port" name]
            | None -> []
        ) parameterNames
    List.append errorList localErrors
/// Checks the names used for wires
/// Throws an error if the name is used for a port 
let wireNameCheck ast portMap parameterSizeMap wireNameList errorList = 
    let localErrors = 
        List.collect (fun name -> 
            match Map.tryFind name portMap with
            | Some found -> [sprintf "Variable %s cannot be used as a wire name because it is declared as a port" name]
            | None -> 
                match Map.tryFind name parameterSizeMap with
                | Some p -> [sprintf "Variable %s cannot be used as a wire name because it is declared as a parameter" name]
                | None -> []
        ) wireNameList
    List.append errorList localErrors

/// Checks whether the assignment variables are declared as output ports 
let assignmentNameCheck ast portMap errorList = 
    let items = ast.Module.ModuleItems.ItemList |> Array.toList
    let names = 
        items |> List.collect (fun x -> 
            match (x.Statement |> isNullOrUndefined) with
            | false -> 
                match x.Statement with
                | Some statement when statement.StatementType = "assign" -> [statement.Assignment.LHS.Primary.Name]
                | _ -> []
            | true -> []
        )
    let localErrors = 
        List.collect (fun name -> 
            match Map.tryFind name portMap with
            | Some found when found = "output"  -> []
            | _ -> [sprintf "Variable %s is not declared as an output port" name]
        ) names
    List.append errorList localErrors

/// Checks if all declared ports have a value assigned to them
/// The check is done bit-by-bit
let checkAllOutputsAssigned ast portMap portSizeMap errorList =
    
    // List of declared ports, bit by bit
    let outputPortListMap = 
        portMap 
        |> Map.filter (fun n s -> s = "output") 
        |> Map.toList 
        |> List.map fst
        |> List.collect (fun x -> 
            let size = Map.find x portSizeMap
            let names = [0..size-1] |> List.map (fun y -> (x+(string y),x))
            names 
        )

    let outputPortList = List.map fst outputPortListMap

    // List of assignments in the form of (port name, BitsStart, BitsEnd)
    let assignments = 
        ast.Module.ModuleItems.ItemList
        |> Array.toList 
        |> List.collect (fun x -> 
            match (x.Statement |> isNullOrUndefined) with
            | false -> 
                match x.Statement with
                | Some statement when statement.StatementType = "assign" -> [statement.Assignment.LHS]
                | _ -> []
            | true -> []
        )
        |> List.map (fun assignment ->
            match assignment with
            | a when isNullOrUndefined assignment.BitsStart -> (a.Primary.Name,-1,-1)
            | a -> (a.Primary.Name,(int (Option.get a.BitsStart)),(int (Option.get a.BitsEnd)))
        )
    
    
    // List of assigned ports, bit by bit
    let assignmentPortListMap =
        assignments
        |> List.collect ( fun x ->
            match x with
            |(name,-1,-1)->
                match Map.tryFind name portSizeMap with
                | Some size -> 
                    let names = [0..size-1] |> List.map (fun y -> (name+(string y),name))
                    names
                | None -> []
            |(name,x,y) when x=y ->
                [(name+(string x),name)]
            |(name,bStart,bEnd)->
                let names = [bEnd..bStart] |> List.map (fun y -> (name+(string y),name))
                names
        )
    let assignmentPortList = List.map fst assignmentPortListMap
    
    /// Returns the unassigned port names given the output port list and the assigned port list 
    let diffChecker exclude lst mapping message errorList =
        let diff = List.except (List.toSeq exclude) (lst)
        match List.isEmpty diff with
        |true -> errorList
        |false -> 
            // transform names from "b2" to "b[2]" 
            let unassignedPorts = 
                diff 
                |> List.collect(fun x ->
                    match Map.tryFind x (Map.ofList mapping) with
                    | Some name -> 
                        let length = (Seq.except name x) |> Seq.map string |> String.concat ""
                        [name+"["+length+"]"]
                    | None -> []
                )
            List.append errorList [sprintf "%s: %A" message unassignedPorts]

    let localErrors =
        []
        |> diffChecker assignmentPortList outputPortList outputPortListMap "The following ports are unassigned"
        // |> diffChecker outputPortList assignmentPortList assignmentPortListMap "The following ports are assigned, but not declared as output ports" 
    List.append errorList localErrors

let getPortSizeMap ast = 
    let items = ast.Module.ModuleItems.ItemList |> Array.toList
    items |> List.collect (fun x -> 
            match (x.IODecl |> isNullOrUndefined) with
            | false -> 
                match x.IODecl with
                | Some d -> 
                    let size = 
                        match isNullOrUndefined d.Range with
                        | true -> 1
                        | false -> ((Option.get d.Range).Start |> int) - ((Option.get d.Range).End |> int) + 1
                    d.Variables 
                    |> Array.toList 
                    |> List.collect (fun x -> [(x.Name,size)]) 
                | None -> []
            | true -> []
    ) |> Map.ofList



let getPortMap ast = 
    let items = ast.Module.ModuleItems.ItemList |> Array.toList
    items |> List.collect (fun x -> 
            match (x.IODecl |> isNullOrUndefined) with
            | false -> 
                match x.IODecl with
                | Some d -> 
                    d.Variables 
                    |> Array.toList 
                    |> List.collect (fun x -> [(x.Name,d.DeclarationType)]) 
                | None -> []
            | true -> []
    ) |> Map.ofList


////// NOT FINISHED : TODO ADD RANGE
let getParameterSizeMap ast = 
    let items = ast.Module.ModuleItems.ItemList |> Array.toList
    items |> List.collect (fun x -> 
            match (x.ParamDecl |> isNullOrUndefined) with
            | false -> 
                match x.ParamDecl with
                | Some p -> 
                    let size = 1 ////// FOR NOW 
                        // match isNullOrUndefined d.Range with
                        // | true -> 1
                        // | false -> ((Option.get d.Range).Start |> int) - ((Option.get d.Range).End |> int) + 1
                    [(p.Parameter.Identifier.Name,size)] 
                    // |> Array.toList 
                    // |> List.collect (fun x -> [(x,size)]) 
                | None -> []
            | true -> []
    ) |> Map.ofList

/// Returns the names of the declared WIRES
let getWireNames ast = 
    let items = ast.Module.ModuleItems.ItemList |> Array.toList
    items |> List.collect (fun x -> 
        match (x.Statement |> isNullOrUndefined) with
        | false -> 
            match x.Statement with
            | Some statement when statement.StatementType = "wire" -> [statement.Assignment.LHS.Primary.Name]
            | _ -> []
        | true -> []
    )


let getErrors ast model=
    printfn "Parsed input: %A" ast
    let portMap  = getPortMap ast
    let portSizeMap = getPortSizeMap ast
    let parameterSizeMap = getParameterSizeMap ast
    let wireNameList = getWireNames ast
    let parameterNameList = parameterSizeMap |> Map.toList |> List.map fst
    printfn "Port size map: %A" portSizeMap
    []
    |> nameCheck ast
    |> portCheck ast portMap
    |> parameterNameCheck ast parameterNameList portMap
    |> wireNameCheck ast portMap parameterSizeMap wireNameList
    |> assignmentNameCheck ast portMap
    |> checkAllOutputsAssigned ast portMap portSizeMap