////////////////////////////////////////////////////////////////////////////////
// 
// LL1 Parser Table Building Instruction Tool
//
// A Teaching tool for showing how to construct the First and Last tables for a 
// LL1 Parser, given a context free grammar. This program walks through each 
// step for building out the tables and attempts to give reasoning and
// instructions to the user on how to construct the tables.
//
// Nathan Hampton
// Spring 2025
//
////////////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////////////
// Global Constants
////////////////////////////////////////////////////////////////////////////////

const epsilon = "e";
const grammarProductionColumn = "GrammarProductionColumn";
const productionTableID = "grammarTable";
const grammarInputBox = "UserGrammar";
const firstTableDiv = "firstTableDiv";
const firstTableID = "firstTable";
const followTableDiv = "followTableDiv";
const followTableID = "followTable";
const followRulesID = "followRules";
const lastTableDiv = "lastTableDiv";
const lastTableID = "lastTable";
const messageTableID = "Instructions"
const messageParent="MessageTable"
const headingTable="Table_1"
const emptyCell = ".";
const nullableColumnKey = "Nullable";
const leftRecursionErrorStr = "Left Recursion Detected, Cannot Continue! The Grammar is not LL(1) Parsable!";
const unparsableGrammarErrorStr = "The Grammar is not LL(1) Parsable!";
const defaultGrammar2 = [
    "D ::= R",
    "R ::= B C",
    "B ::= +",
    "B ::= e",
    "C ::= -",
    "C ::= e",
].join("\n");

const defaultGrammar3 = [
    "D ::= R + D",
    "D ::= num",
    "R ::= ( B + R a)",
    "R ::= @ B + C @",
    "R ::= B C",
    "R ::=  e",
    "B ::= qqq",
    "B ::=  e",
    "C ::= *",
].join("\n");

const defaultGrammar = [
    "<Prog> ::= { <Stmts> }",
    "<Stmts> ::= <Stmt> <Stmts> ",
    "<Stmts> ::= e",
    "<Stmt> ::= id = <Expr> ;",
    "<Stmt> ::= if ( <Expr> ) <Stmt>",
    "<Expr> ::= id <Etail>",
    "<Etail> ::= + <Expr>",
    "<Etail> ::= - <Expr>",
    "<Etail> ::= e",
].join("\n");

// Colors to use for tables
enum HTMLColors  {
    defaultColor   = "white",
    disableColor   = "gray",
    highlightColor = "yellow",
    softGreyColor  = "#e4e3e3",
    errorColor = "red",
    textColor = "black",
    epsilonColor = "#dbdbdb"
}

// Cell State attributes
enum CellAttr {
    needsSimplified = "data-NeedsSimplified",
    needsFilled = "data-NeedsFilled",
    parentCellCol = "data-ParentCellCol",
    childCellCol = "data-ChildCellCol",
    prodRuleData = "data-ProductionRuleData",
    styleOverride = 'data-StyleOverride'
}

// Steps enum
enum Steps {
    INVALID                         = -1,
    ENTER_GRAMMAR                   = 0, // User Enters Grammar
    ENTER_EPSILON                   = 1, // Select and find all direct productions of epsilon
    ENTER_EPSILON_FROM_EPSILON      = 2, // Select and find all indirect productions of epsilon
    FIND_FIRSTS                     = 3, // Find the First value of each production
    FIND_FIRSTS_COMPUTED            = 4, // Backfill the first values as needed
    FIND_FOLLOWS                    = 5,
    FIND_FOLLOWS_COMPUTED_FIRSTS    = 6,
    FIND_FOLLOWS_COMPUTED_FOLLOWS   = 7,
    PLACE_FOLLOW_EPSILON_NUMBERS    = 8,
    CREATE_FINAL_TABLE              = 9,
    DONE                            = 10
};

enum FollowRuleType {
    TERMINAL_FOLLOWS     = 0,
    NON_TERMINAL_FOLLOWS = 1,
    END_OF_PRODUCTION    = 2,
    FIRST_SIMPLIFY       = 3,
    FOLLOW_SIMPLIFY       = 3,
}

////////////////////////////////////////////////////////////////////////////////
// Global Variables
////////////////////////////////////////////////////////////////////////////////

var grammar: Grammar;
var currentStep: number = Steps.ENTER_GRAMMAR;
var productionTable: ProductionTable;
var firstTable: FirstTable;
var followTable: FollowTable;
var instructionString: string = '';
var errorString: string = '';
var errorState: boolean = false
var selectedProductionFollowCells: Map<FollowRuleType, Set<FollowCellSelection>> = new Map([
    [FollowRuleType.TERMINAL_FOLLOWS, new Set()],
    [FollowRuleType.NON_TERMINAL_FOLLOWS, new Set()],
    [FollowRuleType.END_OF_PRODUCTION, new Set()],
    [FollowRuleType.FIRST_SIMPLIFY, new Set()],
    [FollowRuleType.FOLLOW_SIMPLIFY, new Set()],
]);
var FollowRules: Map<FollowRuleType, string> = new Map([
    [FollowRuleType.TERMINAL_FOLLOWS, "A non-terminal followed by a terminal."],
    [FollowRuleType.NON_TERMINAL_FOLLOWS, "A non-terminal followed by a non-terminal."],
    [FollowRuleType.END_OF_PRODUCTION, "A non-terminal at the end of a production."],
])
var first_pass = true;

////////////////////////////////////////////////////////////////////////////////
//  HTML Helper Functions
////////////////////////////////////////////////////////////////////////////////

function deleteMyTable(myTableId: string) {
    var element = document.getElementById(myTableId);
    if(element != null)
        element.parentNode!.removeChild(element);
}


// Set the string in the instruction field
function setInstructionValue(value: string, clear:boolean = true){
    var instructions = document.getElementById(messageTableID) as HTMLHeadingElement;
    instructionString = value;
    if (clear){
        errorString = ''
    }
    instructions.textContent = [instructionString, errorString].join("\n");
}

// Set an Error value in the instruction field.
function setErrorValue(value: string){
    var instructions = document.getElementById(messageTableID) as HTMLHeadingElement;
    errorString = value;
    instructions.textContent = [instructionString, errorString].join("\n");
}

// Get the non-terminal row key from a string of type 'First(<non-term>)' or
// 'Follow(<non-term>)' 
function extractRowKey(value: string|null): string|null{
    if (value == null){
        return null;
    }
    const regex = /(?:(?:First|Follow)\((?<row>.*)\))/
    const found = value.match(regex);
    if (found != null){
        const row = found.groups?.row;
        if (row == null){
            return null;
        }
        return row
    }
    return null;
}

////////////////////////////////////////////////////////////////////////////////
// Grammar Processing Classes
////////////////////////////////////////////////////////////////////////////////

// Define a type representing a production rule in a grammar.
// Each rule has a left-hand side (non-terminal) and a right-hand side (an array of symbols).
type ProductionRule = {
    left: string;        // The left-hand side (LHS) non-terminal.
    right: string[];     // The right-hand side (RHS) as an array of symbols (terminals or non-terminals).
    // cellPos: CellPos;
};

// Define a type representing the overall grammar.
type Grammar = {
    terminals: Set<string>;                       // Set of terminal symbols.
    nonTerminals: Set<string>;                    // Set of non-terminal symbols.
    rules: ProductionRule[];                      // List of production rules.
    firstSets: Map<string, Set<string>>;          // Map from each symbol to its FIRST set.
    followSets: Map<string, Set<string>>;         // Map from each non-terminal to its FOLLOW set.
    solvedFirstSets: Set<string>;                 // Marks what first sets have been solved
};

// The data for a single row in the production table
type ProductionRow = {
    idx: number;
    rule: ProductionRule;
    enabled: boolean;
    color: string;
}

// Represents the current state of the Production Table
class ProductionTable {
    tableID: string;
    productions: ProductionRow[];
    selectedProduction: number|null;
    table: HTMLTableElement;
    parentID: string;

    constructor(parentID: string, grammar: Grammar){
        this.tableID = productionTableID;
        this.productions = new Array<ProductionRow>();
        for (const [idx, rule] of grammar.rules.entries()){
            this.productions.push({
                idx:idx,
                rule:rule,
                enabled:true,
                color: HTMLColors.defaultColor
            })
        }
        this.selectedProduction = null;
        this.table = document.createElement("TABLE") as HTMLTableElement;
        this.parentID = parentID;
        this.render();
    }

    _setRowCallback(row: HTMLTableRowElement, rowIdx: number, table: ProductionTable){
        row.onclick = function(){ table.buttonCallback(rowIdx)};
        row.style.cursor = "pointer"
    }

    render() {
        // Remove old table
        deleteMyTable(this.tableID)
        // Create a new one based on the current state
        this.table = document.createElement("TABLE") as HTMLTableElement;
        this.table.setAttribute("id", this.tableID);
        this.table.style.border = "2px solid black";
        this.table.style.backgroundColor = HTMLColors.defaultColor;
        // Add Header
        var header = document.createElement("caption");
        header.textContent = "Production Table";
        header.style.textAlign = "center";
        header.style.fontSize = "large";
        header.style.border = "2px solid black";
        header.style.backgroundColor = HTMLColors.softGreyColor;
        this.table.caption = header;
        // Build Rows and columns
        for(var y = 0; y < this.productions.length; y++){
            var prod = this.productions[y];
            var newRow = document.createElement("TR") as HTMLTableRowElement;
            if (prod.enabled){
                this._setRowCallback(newRow, y, this)
            }
            //     this.ButtonCallback(prod.idx);
            // }};
            newRow.setAttribute("id", prod.rule.left + " ::= " + prod.rule.right.join(""));
            newRow.style.border = "1px solid black";
            // Create index cell
            var idxCell = document.createElement("TD") as HTMLTableCellElement;
            idxCell.style.width = "24px";
            idxCell.style.border = "1px solid black";
            idxCell.style.color = "black";
            idxCell.style.backgroundColor = HTMLColors.softGreyColor;
            idxCell.textContent = y.toString();
            newRow.appendChild(idxCell);
            // Create Cell
            var cell = document.createElement("TD") as HTMLTableCellElement;
            newRow.appendChild(cell);
            cell.style.width = "350px";
            cell.style.border = "1px solid black";
            cell.style.color = "black";
            // Add production rule
            cell.textContent = prod.rule.left + " ::= " + prod.rule.right.join("");
            // Set the row color
            newRow.style.backgroundColor = prod.color;
            this.table.appendChild(newRow);
        }
        // Add the created table back
        var parent = document.getElementById(this.parentID);
        parent?.appendChild(this.table);
    }

    disableAllRows(){
        for(var y = 0; y < this.productions.length; y++){
            this.setProductionRowEnable(y, false);
        }
    }

    setProductionRowEnable(row: number, enable: boolean){
        this.productions[row].enabled = enable;
        if (enable == true){
            this.productions[row].color = HTMLColors.defaultColor;
            this.productions[row].enabled = true;
        }
        else {
            this.productions[row].enabled = false;
            this.productions[row].color = HTMLColors.disableColor;
        }
        if (this.selectedProduction == this.productions[row].idx){
            this.selectedProduction = null;
        }
    }

    selectProductionRow(row: number): boolean {
        if (!this.productions[row].enabled){
            this.selectedProduction = null;
            return false;
        }
        if (this.selectedProduction != null){
            const oldSelection = this.productions[this.selectedProduction];
            if (oldSelection.enabled){
                oldSelection.color = HTMLColors.defaultColor;
            }
        }
        this.selectedProduction = row;
        this.productions[row].color = HTMLColors.highlightColor;
        console.log(`Selected Production Table Row: ${row} `)
        return true;
    }

    buttonCallback(row: number): null {
        if (errorState == true){
            return null;
        }
        const prod = this.productions[row];
        switch (currentStep) {
            // Check if this rule directly produces epsilon
            case Steps.ENTER_EPSILON:
                if (prod.rule.right[0] == epsilon){
                    // This is a valid selection
                    this.selectProductionRow(row);
                    setInstructionValue(
                        "Now select the cell in the first table that corresponds with this non-terminal producing epsilon. "
                    );
                }
                else {
                    setInstructionValue(
                        "The Selected production does not directly produce epsilon! Try again."
                    );
                    // Reset the selected row
                    if (this.selectedProduction != null){
                        this.productions[this.selectedProduction].color = HTMLColors.defaultColor;
                        this.selectedProduction = null;
                    }
                }
                break;

            // Check if this rule in-directly produces epsilon
            case Steps.ENTER_EPSILON_FROM_EPSILON:
                // Check if the selected production rule can be epsilon via all
                // its values
                var indirectlyEpsilon = true;
                for (var i = 0 ; i < prod.rule.right.length; i ++){
                    var indirectEpsilonCol = firstTable.getCell(prod.rule.right[i], epsilon)
                    // var indirectEpsilonCol = getTableCell(
                    //     firstTableID,
                    //     prod.rule.right[i],
                    //     epsilon
                    // )
                    if (indirectEpsilonCol != null){
                        // Check if the value is set
                        if ( indirectEpsilonCol.data != emptyCell){
                            // This letter can produce epsilon check the next
                            continue;
                        }
                        else {
                            indirectlyEpsilon = false;
                            // Not indirectly producible for now, but could be in the future
                            setInstructionValue(
                                "The Selected production rule does not indirectly produce epsilon currently! Try again."
                            );
                            // Reset the selected row
                            if (this.selectedProduction != null){
                                this.productions[this.selectedProduction].color = HTMLColors.defaultColor;
                                this.selectedProduction = null;
                            }
                        }
                    }
                    else {
                        indirectlyEpsilon = false;
                        // Not producible
                        setInstructionValue(
                            "The Selected production rule does not indirectly produce epsilon! Try again."
                        );
                        // Reset the selected row
                        if (this.selectedProduction != null){
                            this.productions[this.selectedProduction].color = HTMLColors.defaultColor;
                            this.selectedProduction = null;
                        }
                    }
                }
                if (indirectlyEpsilon == true){
                    // Can be produced indirectly
                    this.selectProductionRow(row);
                    setInstructionValue(
                        "Now select the cell in the first table that corresponds with the rule producing epsilon."
                    );
                }
                break;

            // Find the first value for this production
            case Steps.FIND_FIRSTS:
                this.selectProductionRow(row);
                // Check where this production rule should be placed
                var instructions = new Array<string>();

                for (var i = 0; i < prod.rule.right.length; i++){
                    if (grammar.terminals.has(prod.rule.right[i])){
                        instructions.push(
                            `First(${prod.rule.left}) ::= '${prod.rule.right[i]}'. So put a ${row} at the intersection of ${prod.rule.left} and ${prod.rule.right[i]} in the First Table.`
                        )
                        break;
                    }
                    else {
                        instructions.push(
                            `First(${prod.rule.left}) ::= 'First(${prod.rule.right[i]})'. So put a ${row} at the intersection of ${prod.rule.left} and First(${prod.rule.right[i]}) in the First Table.`
                        )
                        // Check if this is nullable
                        var epsilonCell = firstTable.getCell(prod.rule.right[i], epsilon)
                        if (epsilonCell == null){
                            break;
                        }
                        // var epsilonCell = getTableCell(firstTableID, prod.rule.right[i], epsilon);
                        if (epsilonCell.data != emptyCell){
                            if (prod.rule.right.length-1 != i){
                                instructions.push(
                                    `Note that ${prod.rule.right[i]} is nullable, So we must also look at the next symbol in the production.`
                                )
                            }
                        }
                        else{
                            break;
                        }
                    }
                }
                setInstructionValue(instructions.join("\n"));

                break;

            case Steps.FIND_FOLLOWS:
                var validRow = false;
                for (const symbol of prod.rule.right.values()){
                    if (grammar.nonTerminals.has(symbol)){
                        validRow = true;
                        break;
                    }
                }
                if (!validRow){
                    break;
                }
                // Select the row
                this.selectProductionRow(row);
                // Disable all rules to start with
                for (const [key, value] of selectedProductionFollowCells.entries()){
                    followTable.rulesData[key] = false;
                    selectedProductionFollowCells.set(key, new Set());
                }
                followTable.selectedRule = null;
                // Fill out the follow table selections that need to be made
                // for this production
                for (const [idx, symbol] of prod.rule.right.entries()) {
                    // Check if its a terminal
                    if (grammar.terminals.has(symbol)){
                        // Nothing to do for a terminal
                        continue;
                    }
                    // Check if this is the last symbol
                    if (prod.rule.right.length <= idx+1){
                        // Last Symbol, Need to add Follow(LHS)
                        selectedProductionFollowCells.get(FollowRuleType.END_OF_PRODUCTION)?.add({
                            rowLabel: symbol,
                            columnLabel: `Follow(${prod.rule.left})`
                        })
                        followTable.rulesData[FollowRuleType.END_OF_PRODUCTION] = true;
                        console.log(`Adding rule END_OF_PRODUCTION: Row ${symbol} , Column Follow(${prod.rule.left})`)
                        continue;
                    }
                    const followingSymbol = prod.rule.right[idx+1];
                    // Check if the following symbol is terminal
                    if (grammar.terminals.has(followingSymbol)){
                        // Terminal follows, Add the terminal
                        selectedProductionFollowCells.get(FollowRuleType.TERMINAL_FOLLOWS)?.add({
                            rowLabel: symbol,
                            columnLabel: followingSymbol
                        })
                        followTable.rulesData[FollowRuleType.TERMINAL_FOLLOWS] = true;
                        console.log(`Adding rule TERMINAL_FOLLOWS: Row ${symbol} , Column ${followingSymbol}`)
                        continue;
                    };
                    // Check for a non-terminal
                    if (grammar.nonTerminals.has(followingSymbol)){
                        // Non-Terminal follows, Add its First set
                        selectedProductionFollowCells.get(FollowRuleType.NON_TERMINAL_FOLLOWS)?.add({
                            rowLabel: symbol,
                            columnLabel: `First(${followingSymbol})`
                        })
                        followTable.rulesData[FollowRuleType.NON_TERMINAL_FOLLOWS] = true;
                        console.log(`Adding rule NON_TERMINAL_FOLLOWS: Row ${symbol} , Column First(${followingSymbol})`)
                        continue;
                    }
                }
                // Update the instructions
                setInstructionValue(
                    "Now select a rule in the Follow Rules table that applies to this production."
                )
                followTable.render();
                break;
            default:
                break;
        }
        this.render()
        return null;
    }
}

// Represents the data for a single cell in a first or last table
type CellData = {
    color: HTMLColors,
    enabled: boolean,
    data: string
    attributes: Map<string,string>
}

function resetError(){
    errorState = false
    setInstructionValue("", true);
    var instructions = document.getElementById(messageTableID) as HTMLHeadingElement;
    instructions.style.color = HTMLColors.textColor;
    var messageBox = document.getElementById(messageParent) as HTMLDivElement;
    messageBox.style.backgroundColor = HTMLColors.softGreyColor
}

// Error state caused by a left recursion
function grammarUnparsableError(errorStr: string){
    setInstructionValue("", true);
    var instructions = document.getElementById(messageTableID) as HTMLHeadingElement;
    instructions.style.color = HTMLColors.defaultColor;
    var messageBox = document.getElementById(messageParent) as HTMLDivElement;
    messageBox.style.backgroundColor = HTMLColors.errorColor
    setErrorValue(errorStr)
    firstTable.disableAllCells();
    followTable.disableAllCells();
    productionTable.disableAllRows();
    firstTable.colorAllCells(HTMLColors.disableColor);
    followTable.colorAllCells(HTMLColors.disableColor);
    firstTable.render();
    followTable.render();
    productionTable.render();
}


// Class for interacting with the first table
class FirstTable {
    parentID: string;
    tableID: string;
    columns: string[];
    rows: string[];
    table: HTMLTableElement;
    tableData: Map<string,Map<string,CellData>>;
    tableHeaderStr: string = "First Table";

    constructor(grammar: Grammar){
        this.parentID = firstTableDiv;
        this.tableID = firstTableID;
        this.columns = new Array<string>();
        this.rows = new Array<string>();
        this.table = document.createElement("TABLE") as HTMLTableElement;
        grammar.nonTerminals.forEach((nonTerm) => {
            this.rows.push(nonTerm);
        })
        grammar.terminals.forEach((term) => {
            this.columns.push(term);
        })
        grammar.nonTerminals.forEach((value, key, map) =>{
            this.columns.push(`First(${value})`)
        })
        this.columns.push(epsilon);
        this.tableData = new Map<string,Map<string,CellData>>;
        this.rows.forEach((row) => {
            var newColumn = new Map<string,CellData>();
            this.columns.forEach(
                (column) => {
                    newColumn.set(
                        column,
                        {
                            color: HTMLColors.defaultColor,
                            enabled: true,
                            data: emptyCell,
                            attributes: new Map()
                        }
                    );
                }
            )
            this.tableData.set(row, newColumn);
        })
        this.render()
    }

    setTableHeaderColor(color: HTMLColors){
        var header = this.table.caption;
        if (header != null){
            header.style.backgroundColor = color;
        }
    }

    // Internal method for setting callback of cells
    _setTableCellCallback(
        cell: HTMLTableCellElement,
        table: FirstTable, rowLabel: string, columnLabel: string,
        ) {
        cell.onclick = function(){table.cellCallback(rowLabel, columnLabel)};
        cell.style.cursor = "pointer"
    }

    // Render the table
    render(){
        // Remove old table
        deleteMyTable(this.tableID)
        // Create a new one based on the current state
        this.table = document.createElement("TABLE") as HTMLTableElement;
        this.table.setAttribute("id", this.tableID);
        this.table.style.border = "2px solid black";
        this.table.style.backgroundColor = HTMLColors.defaultColor;
        this.table.style.borderCollapse = "separate";
        // Add header
        var header = document.createElement("caption");
        header.textContent = this.tableHeaderStr
        header.style.textAlign = "center";
        header.style.fontSize = "large";
        header.style.border = "2px solid black";
        header.style.backgroundColor = HTMLColors.softGreyColor;
        this.table.caption = header;
        // Build Rows
        for(var r = 0; r < this.rows.length+1; r++){
            var newRow = document.createElement("TR") as HTMLTableRowElement;
            this.table.appendChild(newRow);
            if (r == 0){
                newRow.setAttribute("data-row", "HeaderRow");
            }
            else{
                newRow.setAttribute("data-row", this.rows[r-1]);
            }
            for (var c = 0; c < this.columns.length+1; c++){
                var cell = document.createElement("TD") as HTMLTableCellElement;
                cell.style.color = "black";
                newRow.appendChild(cell);
                cell.style.minWidth = "50px";
                cell.style.border = "1px solid black";
                // Check if this is the header row
                if (r == 0){
                    // Set header elements
                    if (c == 0 ){
                        cell.setAttribute("data-column", "RowLabelColumn");
                        cell.textContent = ""
                        cell.style.backgroundColor = HTMLColors.softGreyColor;
                    }
                    else {
                        cell.setAttribute("data-column", this.columns[c-1]);
                        // Set the Column Headers
                        cell.textContent = this.columns[c-1]
                        cell.style.backgroundColor = HTMLColors.softGreyColor;
                    }
                }
                else{
                    if (c == 0){
                        // Set Row labels
                        cell.setAttribute("data-column", "RowLabelColumn");
                        cell.textContent = this.rows[r-1];
                        cell.style.backgroundColor = HTMLColors.softGreyColor;
                    }
                    else {
                        // Build first table cell locations
                        cell.setAttribute("data-column", this.columns[c-1]);
                        var cellData = this.tableData.get(this.rows[r-1])?.get(this.columns[c-1]);
                        if (cellData == null){
                            cellData = {
                                color: HTMLColors.defaultColor,
                                enabled: true,
                                data: emptyCell,
                                attributes: new Map()
                            }
                        }
                        cell.style.backgroundColor = cellData.color
                        cell.textContent = cellData.data;
                        // Add additional coloring for the epsilon column
                        if (this.columns[c-1] === epsilon){
                            if (cell.style.backgroundColor == HTMLColors.defaultColor){
                                // Epsilon should be a slightly darker color
                                cell.style.backgroundColor = HTMLColors.epsilonColor;
                            }
                        }
                        // Add cell attributes
                        for (const [key, value] of cellData.attributes.entries()){
                            cell.setAttribute(key, value);
                        }
                        if (cellData.enabled){
                            // Add callback
                            this._setTableCellCallback(
                                cell, this, this.rows[r-1], this.columns[c-1]
                            )
                        }
                    }
                }
            }
        }
        var parent = document.getElementById(this.parentID);
        parent?.appendChild(this.table);
    }

    setCellEnable(rowLabel: string, columnLabel: string, enable:boolean){
        var cellData = this.tableData.get(rowLabel)?.get(columnLabel);
        if (cellData == null){
            cellData = {
                color: HTMLColors.defaultColor,
                enabled: true,
                data: emptyCell,
                attributes: new Map()
            }
        }
        cellData.enabled = enable
        this.tableData.get(rowLabel)?.set(columnLabel, cellData);
    }

    setCellColor(rowLabel: string, columnLabel: string, color:HTMLColors) {
        var cellData = this.tableData.get(rowLabel)?.get(columnLabel);
        if (cellData == null){
            cellData = {
                color: HTMLColors.defaultColor,
                enabled: true,
                data: emptyCell,
                attributes: new Map()
            }
        }
        cellData.color = color
        this.tableData.get(rowLabel)?.set(columnLabel, cellData);
    }

    disableAllCells(){
        for(const [rowKey, columns] of this.tableData.entries()){
            for (const [columnKey, cell] of columns.entries()){
                cell.enabled = false;
                this.tableData.get(rowKey)?.set(columnKey, cell);
            }
        }
    }

    colorAllCells(color: HTMLColors){
        for(const [rowKey, columns] of this.tableData.entries()){
            for (const [columnKey, cell] of columns.entries()){
                cell.color = color;
                this.tableData.get(rowKey)?.set(columnKey, cell);
            }
        }
    }

    setCellValue(rowLabel: string, columnLabel: string, data:string){
        var cellData = this.tableData.get(rowLabel)?.get(columnLabel);
        if (cellData == null){
            cellData = {
                color: HTMLColors.defaultColor,
                enabled: true,
                data: emptyCell,
                attributes: new Map()
            }
        }
        cellData.data = data
        this.tableData.get(rowLabel)?.set(columnLabel, cellData);
    }

    setCell(rowLabel: string, columnLabel: string, cellData: CellData){
        this.tableData.get(rowLabel)?.set(columnLabel, cellData);
    }

    getCell(rowLabel: string, columnLabel: string): CellData|null {
        const row = this.tableData.get(rowLabel);
        if (row == null){
            return null;
        }
        const cell = row.get(columnLabel);
        if (cell == null){
            return null;
        }
        return cell;
    }
    // FirstTable cell Callback
    cellCallback(rowLabel: string, columnLabel: string) {
        if (errorState == true){
            return;
        }
        // var cell = getTableCell(this.tableID, rowLabel,columnLabel);
        var selectedCellData = this.getCell(rowLabel, columnLabel);
        // if (cell == null){
        //     return;
        // }
        switch (currentStep) {
            case Steps.ENTER_EPSILON:
                // Check that this cell matches the selected production rule.
                if (productionTable.selectedProduction == null){
                    // No production selected just return
                    return;
                }
                // Check that the selected production rule's left side matches
                // the row label
                var selected_prod = productionTable.productions[productionTable.selectedProduction];
                if (selected_prod.rule.left == rowLabel){
                    // Correct row, Check that this is the epsilon column
                    if (columnLabel == epsilon){
                        // Correct choice, place the choice index in the cell
                        var cellData = this.tableData.get(rowLabel)?.get(columnLabel);
                        if (cellData == null){
                            cellData = {
                                color: HTMLColors.defaultColor,
                                enabled: true,
                                data: emptyCell,
                                attributes: new Map()
                            }
                        }
                        cellData.data = productionTable.selectedProduction.toString();
                        this.tableData.get(rowLabel)?.set(columnLabel, cellData);
                        this.render();
                        checkProgress();
                    } else {
                        // Not the epsilon column
                        setInstructionValue(
                            "The production rule should be placed in the epsilon column!"
                        )
                    }
                } else {
                    // Not the correct row
                    setInstructionValue(
                        `The production rule should be placed in the ${selected_prod.rule.left} row!`
                    )
                }
                break;

            case Steps.ENTER_EPSILON_FROM_EPSILON:
                 // Check that this cell matches the selected production rule.
                 if (productionTable.selectedProduction == null){
                    // No production selected just return
                    return;
                }
                // Check that the selected production rule's left side matches
                // the row label
                var selected_prod = productionTable.productions[productionTable.selectedProduction];
                if (selected_prod.rule.left == rowLabel){
                    // Correct row, Check that this is the epsilon column
                    if (columnLabel == epsilon){
                        // Correct choice, place the choice index in the cell
                        var cellData = this.tableData.get(rowLabel)?.get(columnLabel);
                        if (cellData == null){
                            cellData = {
                                color: HTMLColors.defaultColor,
                                enabled: true,
                                data: emptyCell,
                                attributes: new Map()
                            }
                        }
                        cellData.data = productionTable.selectedProduction.toString()
                        this.tableData.get(rowLabel)?.set(columnLabel, cellData);
                        this.render();
                        checkProgress();
                    }
                    else {
                        // Not the epsilon column
                        setInstructionValue(
                            "The production rule should be placed in the epsilon column!"
                        )
                    }
                 } else {
                    // Not the correct row
                    setInstructionValue(
                        `The production rule should be placed in the ${selected_prod.rule.left} row!`
                    )
                }
                break;

            case Steps.FIND_FIRSTS:
                // Check that this cell matches the selected production rule.
                if (productionTable.selectedProduction == null){
                    // No production selected just return
                    return;
                }
                const prod = productionTable.productions[productionTable.selectedProduction];
                // Check that this is the correct row
                if (prod.rule.left != rowLabel){
                    // Not the correct row
                    setErrorValue(
                        `The production rule should be placed in the ${prod.rule.left} row!`
                    )
                }
                else {
                    var stringComplete = false;
                    for (var i = 0; i < prod.rule.right.length; i++ ){
                        var currentSymbol = prod.rule.right[i];
                        if (grammar.terminals.has(currentSymbol)){
                            if (columnLabel == currentSymbol){
                                // We should place the symbol
                                var cellData = this.tableData.get(rowLabel)?.get(columnLabel);
                                if (cellData == null){
                                    cellData = {
                                        color: HTMLColors.defaultColor,
                                        enabled: true,
                                        data: emptyCell,
                                        attributes: new Map()
                                    }
                                }
                                cellData.data = productionTable.selectedProduction.toString()
                                this.tableData.get(rowLabel)?.set(columnLabel, cellData);
                                this.render();
                                checkProgress();
                                setErrorValue("");
                                stringComplete = true;
                                break;
                            }
                            else{
                                setErrorValue(
                                    `The production rule should be placed in the ${currentSymbol} column!`
                                )
                                break;
                            }
                        }
                        else {
                            var correctColumn = `First(${currentSymbol})`;
                            if (correctColumn == columnLabel){
                                // We should place the symbol
                                var cellData = this.tableData.get(rowLabel)?.get(columnLabel);
                                if (cellData == null){
                                    cellData = {
                                        color: HTMLColors.defaultColor,
                                        enabled: true,
                                        data: emptyCell,
                                        attributes: new Map()
                                    }
                                }
                                cellData.data = productionTable.selectedProduction.toString()
                                this.tableData.get(rowLabel)?.set(columnLabel, cellData);
                                this.render();
                                checkProgress();
                                stringComplete = true;
                                setErrorValue("");
                                break;
                            }
                            else {
                            var epsilonCell = firstTable.getCell(currentSymbol, epsilon)
                                // Only continue if the symbol is nullable
                                // var epsilonCell = getTableCell(
                                //     firstTableID,
                                //     currentSymbol,
                                //     epsilon
                                // )
                                if (epsilonCell?.data != emptyCell){
                                    continue;
                                }
                                else {
                                    setErrorValue(
                                        `Incorrect column! Try again`
                                    );
                                    stringComplete = true;
                                    break;
                                }
                            }
                        }
                    }
                    if (!stringComplete){
                        setErrorValue(
                            `Incorrect column! Try again`
                        );
                        break;
                    }
                }
                break;

            case Steps.FIND_FIRSTS_COMPUTED:
                if (selectedCellData == null){
                    return;
                }
                // Check if this a a value that needs to be simplified or one
                // that is a production of the backfill simplification
                if (selectedCellData.attributes.has(CellAttr.needsSimplified)){
                    // Check what values this First Column can be simplified into
                    const columnSymbol = extractRowKey(columnLabel);
                    if (columnSymbol == null){
                        console.error("Column Symbol could not be found!");
                        return;
                    }
                    const childFirstSet = grammar.firstSets.get(columnSymbol);
                    if (childFirstSet == null){
                        break;
                    }
                    // Highlight and enable each cell that can be simplified
                    // into that isn't already simplified
                    var childCellCols = new Array<string>;
                    for (const childSymbol of childFirstSet.values() ){
                        // Check if this value is already filled
                        var childCellData = this.getCell(
                            rowLabel,
                            childSymbol,
                        )
                        if (childCellData == null){
                            continue;
                        }
                        // Check for a double fill of epsilon
                        if (childSymbol == epsilon){
                            if (childCellData.data != emptyCell){
                                continue;
                            }
                        }
                            childCellData.color = HTMLColors.highlightColor
                            childCellData.enabled = true;
                            childCellCols.push(childSymbol);
                            childCellData.attributes.set(CellAttr.needsFilled, selectedCellData.data);
                            var currentParentCols = childCellData.attributes.get(CellAttr.parentCellCol);
                            if (currentParentCols == null){
                                currentParentCols = "[]";
                            }
                            var currentParentColsArray = JSON.parse(currentParentCols) as Array<string>;
                            currentParentColsArray.push(columnLabel);
                            childCellData.attributes.set(CellAttr.parentCellCol, JSON.stringify(currentParentColsArray));
                            this.setCell(rowLabel, childSymbol, childCellData);
                    }
                    // Mark the list of child cells that need to be filled for this cell
                    // to be complete
                    selectedCellData.attributes.set(CellAttr.childCellCol, JSON.stringify(childCellCols));
                    this.setCell(rowLabel,columnLabel, selectedCellData);
                    // Fill out the instructions
                    setInstructionValue(
                        [
                        `For ${columnLabel}: Fill in any values in ${rowLabel} row where they are also filled in `,
                        `the ${columnSymbol} row. We place a ${selectedCellData.data} `,
                        `in the cell to show that production ${selectedCellData.data} can produce that value as its first value.`
                        ].join("")
                    )
                }
                else if (selectedCellData.attributes.has(CellAttr.needsFilled)) {
                    // Selected cell needs filled, Fill the cell
                    const fillData = selectedCellData.attributes.get(CellAttr.needsFilled);
                    if (fillData == null){
                        break;
                    }
                    // Check for left Recursion
                    if (selectedCellData.data != emptyCell && selectedCellData.data != fillData){
                        if (selectedCellData.data != fillData){
                            grammarUnparsableError(leftRecursionErrorStr)
                            return;
                        }
                    }
                    selectedCellData.data = fillData;
                    selectedCellData.color = HTMLColors.disableColor;
                    selectedCellData.attributes.delete(CellAttr.needsFilled);
                    this.setCell(rowLabel, columnLabel, selectedCellData);
                    // Check if the parent cell is done
                    const parentCellCols = JSON.parse(selectedCellData.attributes.get(CellAttr.parentCellCol) as string) as Array<string>;
                    for (var parentCellCol of parentCellCols.values()){
                        var parentCell = this.getCell(rowLabel, parentCellCol);
                        if (parentCell == null){
                            break;
                        }
                        const childJson = parentCell.attributes.get(CellAttr.childCellCol);
                        if (childJson == null){
                            break
                        }
                        var childCells = JSON.parse(childJson) as Array<string>;
                        childCells = childCells.filter(childCol => childCol !== columnLabel);
                        if (childCells.length == 0 ){
                            // Cell complete, Remove child attribute, disable parent
                            parentCell.attributes.delete(CellAttr.childCellCol);
                            parentCell.attributes.delete(CellAttr.needsSimplified);
                            parentCell.color = HTMLColors.disableColor;
                            parentCell.enabled = false;
                            parentCell.data = emptyCell;
                            // Update the instruction box
                            setInstructionValue(
                                "Good Job, now select another cell highlighted in red."
                            )
                            
                        }
                        else {
                            // Remove this cell from the list of children
                            parentCell.attributes.set(CellAttr.childCellCol, JSON.stringify(childCells));
                        }
                        this.setCell(rowLabel, parentCellCol, parentCell);
                    }
                    this.render()
                }
                checkProgress()
                break;
            
            case Steps.FIND_FOLLOWS_COMPUTED_FIRSTS:
                // Verify that a follow table cell is selected
                if (followTable.selectedCell == null){
                    break;
                }
                // Get the row to place the value in the follow table to
                const followRow = followTable.selectedCell.rowLabel;
                // Check if this is an epsilon column
                if (columnLabel == epsilon){
                    // Nullable, need place to place in the follow column.
                    setInstructionValue(
                        `Place an X in the Follow(${rowLabel}) column.`
                    )
                    // Highlight and enable the cell in the follow table
                    var followCell = followTable.getCell(followRow, `Follow(${rowLabel})`);
                    if (followCell == null){
                        break;
                    }
                    followCell.color = HTMLColors.highlightColor;
                    followCell.enabled = true;
                    followCell.attributes.set("data-FirstParentRow", rowLabel);
                    followTable.setCell(followRow, `Follow(${rowLabel})`, followCell);
                    
                }
                else {
                    setInstructionValue(`Place X in the follow ${columnLabel} column.`);
                    // Highlight and enable the cell in the follow table
                    var followCell = followTable.getCell(followRow, columnLabel);
                    if (followCell == null){
                        break;
                    }
                    followCell.color = HTMLColors.highlightColor;
                    followCell.enabled = true;
                    followCell.attributes.set("data-FirstParentRow", rowLabel);
                    followTable.setCell(followRow, columnLabel, followCell);
                }
                followTable.render();
                firstTable.render();
                break;
            
            case Steps.CREATE_FINAL_TABLE:
                if (selectedCellData == null){
                    break;
                }

                // Get the value from the selected follow table cell
                const followCellInfo = followTable.selectedCell;
                if (followCellInfo == null){
                    break;
                }
                const selectedFollowCell = followTable.getCell(followCellInfo.rowLabel, followCellInfo.columnLabel)
                if (selectedFollowCell == null){
                    break;
                }
                // Check if there is already different a value in this cell
                if (selectedCellData.data != emptyCell && selectedCellData.data != selectedCellData.data){
                    grammarUnparsableError(unparsableGrammarErrorStr);
                }
                // Set the value disable both cells
                selectedCellData.data = selectedFollowCell.data;
                selectedCellData.color = HTMLColors.disableColor;
                selectedCellData.enabled = false;
                selectedFollowCell.color = HTMLColors.disableColor;
                selectedFollowCell.enabled = false;
                followTable.selectedCell = null;
                setInstructionValue("Good Now select another value in the follow table.")
                this.render();
                followTable.render();
                checkProgress()
                break;

            default:
                break;
        }
    }
}

type FollowCellSelection = {
    rowLabel: string,
    columnLabel: string
}

class FollowTable {

    parentID: string;
    tableID: string;
    columns: string[];
    rows: string[];
    table: HTMLTableElement;
    tableData: Map<string,Map<string,CellData>>;
    hidden: boolean;
    renderRules: boolean = true;
    selectedRule: FollowRuleType | null;
    rulesTable: HTMLTableElement;
    rulesData: Array<boolean>;
    selectedCell: FollowCellSelection|null = null;
    solvingFollowSet: Set<string> = new Set();

    constructor(grammar: Grammar){
        this.parentID = followTableDiv;
        this.tableID = followTableID;
        this.hidden = false;
        this.columns = new Array<string>();
        this.rows = new Array<string>();
        this.table = document.createElement("TABLE") as HTMLTableElement;
        this.rulesTable = document.createElement("TABLE") as HTMLTableElement;
        this.selectedRule = null;
        this.rulesData = new Array(false,false,false);
        grammar.nonTerminals.forEach((nonTerm) => {
            this.rows.push(nonTerm);
        })
        grammar.terminals.forEach((term) => {
            this.columns.push(term);
        })
        grammar.nonTerminals.forEach((value, key, map) =>{
            this.columns.push(`First(${value})`)
        })
        grammar.nonTerminals.forEach((value, key, map) =>{
            this.columns.push(`Follow(${value})`)
        })
        this.tableData = new Map<string,Map<string,CellData>>;
        this.rows.forEach((row) => {
            var newColumn = new Map<string,CellData>();
            this.columns.forEach(
                (column) => {
                    newColumn.set(
                        column,
                        {
                            color: HTMLColors.defaultColor,
                            enabled: true,
                            data: emptyCell,
                            attributes: new Map()
                        }
                    );
                }
            )
            this.tableData.set(row, newColumn);
        })
        // By default set S,$, and add it to the follow set
        this.setCellValue("S","$", "X");
        grammar.followSets.set("S", new Set("$"));
        this.render();
    }

    setTableHeaderColor(color: HTMLColors){
        var header = this.table.caption;
        if (header != null){
            header.style.backgroundColor = color;
        }
    }

    setTableHidden(hidden: boolean){
        this.hidden = hidden;
    }

    // Internal method for setting callback of cells
    _setTableCellCallback(cell: HTMLElement,
        table: FollowTable, rowLabel: string, columnLabel: string,) {
        cell.onclick = function(){table.cellCallback(rowLabel, columnLabel)};
        cell.style.cursor = "pointer"
    }

    // Internal method for setting callback of the rule table rows
    _setRuleTableCallback(row: HTMLElement, table: FollowTable, ruleId: number) {
        row.onclick = function(){table.ruleRowCallback(ruleId)};
        row.style.cursor = "pointer"
    }

    // Render the table
    render(){
        // Remove old table
        deleteMyTable(this.tableID)
        deleteMyTable(followRulesID)
        if (this.hidden){
            return;
        }
        // Create a new one based on the current state
        this.table = document.createElement("TABLE") as HTMLTableElement;
        this.table.setAttribute("id", this.tableID);
        this.table.style.border = "2px solid black";
        this.table.style.backgroundColor = HTMLColors.defaultColor;
        // Add header
        var header = document.createElement("caption");
        header.textContent = "Follow Table";
        header.style.textAlign = "center";
        header.style.fontSize = "large";
        header.style.border = "2px solid black";
        header.style.backgroundColor = HTMLColors.softGreyColor;
        this.table.caption = header;
        // Build Rows
        for(var r = 0; r < this.rows.length+1; r++){
            var newRow = document.createElement("TR") as HTMLTableRowElement;
            this.table.appendChild(newRow);
            if (r == 0){
                newRow.setAttribute("data-row", "HeaderRow");
            }
            else{
                newRow.setAttribute("data-row", this.rows[r-1]);
            }
            for (var c = 0; c < this.columns.length+1; c++){
                var cell = document.createElement("TD") as HTMLTableCellElement;
                cell.style.color = "black";
                newRow.appendChild(cell);
                cell.style.minWidth = "50px";
                cell.style.paddingLeft = "8px";
                cell.style.paddingRight = "8px";
                cell.style.border = "1px solid black";
                // Check if this is the header row
                if (r == 0){
                    // Set header elements
                    if (c == 0 ){
                        cell.setAttribute("data-column", "RowLabelColumn");
                        cell.textContent = ""
                        cell.style.backgroundColor = HTMLColors.softGreyColor;
                    }
                    else {
                        cell.setAttribute("data-column", this.columns[c-1]);
                        // Set the Column Headers
                        cell.textContent = this.columns[c-1]
                        cell.style.backgroundColor = HTMLColors.softGreyColor;
                    }
                }
                else{
                    if (c == 0){
                        // Set Row labels
                        cell.setAttribute("data-column", "RowLabelColumn");
                        cell.textContent = this.rows[r-1];
                        cell.style.backgroundColor = HTMLColors.softGreyColor;
                    }
                    else {
                        // Build follow table cell locations
                        cell.setAttribute("data-column", this.columns[c-1]);
                        var cellData = this.tableData.get(this.rows[r-1])?.get(this.columns[c-1]);
                        if (cellData == null){
                            cellData = {
                                color: HTMLColors.defaultColor,
                                enabled: true,
                                data: emptyCell,
                                attributes: new Map()
                            }
                        }
                        cell.style.backgroundColor = cellData.color
                        cell.textContent = cellData.data;
                        // Add additional coloring for the epsilon column
                        if (this.columns[c-1] === epsilon){
                            if (cell.style.backgroundColor == HTMLColors.defaultColor){
                                // Epsilon should be a slightly darker color
                                cell.style.backgroundColor = HTMLColors.epsilonColor;
                            }
                        }

                        // Add cell attributes
                        for (const [key, value] of cellData.attributes.entries()){
                            cell.setAttribute(key, value);
                        }
                        if (cellData.enabled){
                            // Add callback
                            this._setTableCellCallback(
                                cell, this, this.rows[r-1], this.columns[c-1]
                            )
                        }
                        // Override Style
                        if (cellData.attributes.has(CellAttr.styleOverride)){
                            const overrides = cellData.attributes.get(CellAttr.styleOverride);
                            console.log("Cell Overrides: ", overrides);
                            if (overrides != null){
                                const overridesMap = JSON.parse(overrides) as Map<string,string>;
                                for (const [key, value] of Object.entries(overridesMap)){
                                    cell.style.setProperty(key, value);
                                }
                            }
                        }
                    }
                }
            }
        }
        // Attach the tables
        var parent = document.getElementById(this.parentID);
        parent?.appendChild(this.table);
        // Check if we should render the rules table
        if (this.renderRules){
            // Build a Rules table
            this.rulesTable = document.createElement("TABLE") as HTMLTableElement;
            this.rulesTable.setAttribute("id", followRulesID);
            this.rulesTable.style.border = "2px solid black";
            this.rulesTable.style.backgroundColor = HTMLColors.defaultColor;
            this.rulesTable.style.paddingTop = '10px';
            // Add header
            var rulesHeader = document.createElement("caption");
            rulesHeader.textContent = "Follow Rules";
            rulesHeader.style.textAlign = "center";
            rulesHeader.style.fontSize = "large";
            rulesHeader.style.border = "2px solid black";
            rulesHeader.style.backgroundColor = HTMLColors.softGreyColor;
            this.rulesTable.caption = rulesHeader;
            // Build the rules
            for(var r = 0; r < 3; r++) {
                var newRow = document.createElement("TR") as HTMLTableRowElement;
                var rule = FollowRules.get(r);
                if (rule == null){
                    continue;
                }
                newRow.setAttribute("id", r.toString());
                newRow.style.border = "1px solid black";
                // Create index cell
                var idxCell = document.createElement("TD") as HTMLTableCellElement;
                idxCell.style.width = "24px";
                idxCell.style.border = "1px solid black";
                idxCell.style.color = "black";
                idxCell.style.backgroundColor = HTMLColors.softGreyColor;
                idxCell.textContent = r.toString();
                newRow.appendChild(idxCell);
                // Create Cell
                var cell = document.createElement("TD") as HTMLTableCellElement;
                newRow.appendChild(cell);
                cell.style.width = "350px";
                cell.style.border = "1px solid black";
                cell.style.color = "black";
                // Add rule
                cell.textContent = rule;
                // Set the row color
                if (this.selectedRule == r){
                    newRow.style.backgroundColor = HTMLColors.highlightColor;
                    // Set the callback
                    this._setRuleTableCallback(
                        newRow, this, r
                    )
                }
                else if (this.rulesData[r]) {
                    newRow.style.backgroundColor = HTMLColors.defaultColor;
                    // Set the callback
                    this._setRuleTableCallback(
                        newRow, this, r
                    )
                }
                else {
                    newRow.style.backgroundColor = HTMLColors.disableColor;
                }
                this.rulesTable.appendChild(newRow);
            }
            parent?.appendChild(this.rulesTable);
        }
    }

    setCellAttr(rowLabel: string, columnLabel: string, attr:string, value:string){
        var cellData = this.tableData.get(rowLabel)?.get(columnLabel);
        if (cellData == null){
            cellData = {
                color: HTMLColors.defaultColor,
                enabled: true,
                data: emptyCell,
                attributes: new Map()
            }
        }
        cellData.attributes.set(attr, value);
        this.tableData.get(rowLabel)?.set(columnLabel, cellData);
    }

    deleteCellAttr(rowLabel: string, columnLabel: string, attr:string){
        var cellData = this.tableData.get(rowLabel)?.get(columnLabel);
        if (cellData == null){
            cellData = {
                color: HTMLColors.defaultColor,
                enabled: true,
                data: emptyCell,
                attributes: new Map()
            }
        }
        cellData.attributes.delete(attr);
        this.tableData.get(rowLabel)?.set(columnLabel, cellData);
    }


    setCellEnable(rowLabel: string, columnLabel: string, enable:boolean){
        var cellData = this.tableData.get(rowLabel)?.get(columnLabel);
        if (cellData == null){
            cellData = {
                color: HTMLColors.defaultColor,
                enabled: true,
                data: emptyCell,
                attributes: new Map()
            }
        }
        cellData.enabled = enable
        this.tableData.get(rowLabel)?.set(columnLabel, cellData);
    }

    setCellColor(rowLabel: string, columnLabel: string, color:HTMLColors) {
        var cellData = this.tableData.get(rowLabel)?.get(columnLabel);
        if (cellData == null){
            cellData = {
                color: HTMLColors.defaultColor,
                enabled: true,
                data: emptyCell,
                attributes: new Map()
            }
        }
        cellData.color = color
        this.tableData.get(rowLabel)?.set(columnLabel, cellData);
    }

    disableAllCells(){
        for(const [rowKey, columns] of this.tableData.entries()){
            for (const [columnKey, cell] of columns.entries()){
                cell.enabled = false;
                this.tableData.get(rowKey)?.set(columnKey, cell);
            }
        }
    }

    colorAllCells(color: HTMLColors){
        for(const [rowKey, columns] of this.tableData.entries()){
            for (const [columnKey, cell] of columns.entries()){
                cell.color = color;
                this.tableData.get(rowKey)?.set(columnKey, cell);
            }
        }
    }

    setCellValue(rowLabel: string, columnLabel: string, data:string){
        var cellData = this.tableData.get(rowLabel)?.get(columnLabel);
        if (cellData == null){
            cellData = {
                color: HTMLColors.defaultColor,
                enabled: true,
                data: emptyCell,
                attributes: new Map()
            }
        }
        cellData.data = data
        this.tableData.get(rowLabel)?.set(columnLabel, cellData);
    }

    setCell(rowLabel: string, columnLabel: string, cellData: CellData){
        this.tableData.get(rowLabel)?.set(columnLabel, cellData);
    }

    getCell(rowLabel: string, columnLabel: string): CellData|null {
        const row = this.tableData.get(rowLabel);
        if (row == null){
            return null;
        }
        const cell = row.get(columnLabel);
        if (cell == null){
            return null;
        }
        return cell;
    }

    cellCallback(rowLabel: string, columnLabel: string) {
        if (errorState == true){
            return;
        }
        var selectedCellData = this.getCell(rowLabel, columnLabel);
        if (selectedCellData == null){
            return;
        }

        switch (currentStep) {
            case Steps.FIND_FOLLOWS:
                if (this.selectedRule == null) {
                    setErrorValue("You must select a Production and Rule first!");
                    return;
                }
                const selectedProductionCells = selectedProductionFollowCells.get(this.selectedRule);
                if (selectedProductionCells == null){
                    break;
                }
                var correctSelection = false;
                for (var validCell of selectedProductionCells.values()){
                    if (validCell.columnLabel == columnLabel && validCell.rowLabel == rowLabel){
                        correctSelection = true;
                        // Remove it from the list of cells we need
                        selectedProductionCells.delete(validCell);
                        break;
                    }
                }
                // Check if this cell is needed in this step
                if (!correctSelection) {
                    // Invalid Selection
                    setErrorValue("Incorrect cell, Try again.");
                    break;
                }
                // Update the cell
                if (productionTable.selectedProduction == null){
                    break;
                }
                selectedCellData.data = 'X'
                // selectedCellData.data = productionTable.selectedProduction.toString()
                this.setCell(rowLabel, columnLabel, selectedCellData);
                // Add it to the follow set
                var followSet = grammar.followSets.get(rowLabel);
                if (followSet == null){
                    followSet = new Set();
                }
                followSet.add(columnLabel);
                grammar.followSets.set(rowLabel, followSet);
                break;

            case Steps.FIND_FOLLOWS_COMPUTED_FIRSTS:
                // Check if this is a parent cell or child cell
                if (selectedCellData.attributes.has('data-ParentCell')){
                    // Check if we are already solving a First() column
                    if (this.selectedCell != null) {
                        break;
                    }
                    // Select this cell
                    this.selectedCell = {rowLabel:rowLabel, columnLabel:columnLabel};
                    // Clear the current solving set
                    this.solvingFollowSet = new Set();
                    // Clear the highlighted cells in the first table
                    firstTable.colorAllCells(HTMLColors.disableColor);
                    firstTable.disableAllCells();
                    // Find which first table values need to be set in the follow table
                    const firstRowKey = extractRowKey(columnLabel);
                    if (firstRowKey == null){
                        console.error("Column Symbol could not be found!");
                        return;

                    }
                    for (const firstColumnKey of firstTable.columns.values()){
                        var firstCell = firstTable.getCell(firstRowKey, firstColumnKey);
                        if (firstCell == null){
                            continue;
                        }
                        // Check if this cell is set
                        if (firstCell.data == emptyCell){
                            continue;
                        }
                        var followChildColumnKey:string = "";
                        // Get the cell in the follow table that should be set by this cell
                        if (firstColumnKey == epsilon){
                            // The first set can be epsilon, so we need the follow of this value
                            followChildColumnKey = `Follow(${firstRowKey})`;
                        }
                        else {
                            followChildColumnKey = firstColumnKey;
                        }
                        var followCell = followTable.getCell(rowLabel, followChildColumnKey);
                        if (followCell == null){
                            continue;
                        }
                        // Check if its is already set
                        if (followCell.data != emptyCell){
                            continue;
                        }
                        // // Mark what data needs to be set in the follow child cell
                        // followCell.attributes.set(CellAttr.prodRuleData, selectedCellData.data);
                        // Enable and color the first table cell
                        firstTable.setCellColor(firstRowKey, firstColumnKey, HTMLColors.highlightColor);
                        firstTable.setCellEnable(firstRowKey, firstColumnKey, true);
                        // Add it to the solving follow set
                        this.solvingFollowSet.add(followChildColumnKey);
                        
                    }
                }
                // Must be a child cell
                else {
                    // Disable, Color, and place the prod number in the cell
                    followTable.setCellValue(rowLabel,columnLabel, 'X');
                    followTable.setCellColor(rowLabel, columnLabel, HTMLColors.disableColor);
                    followTable.setCellEnable(rowLabel,columnLabel, false);
                    // Disable and color the corresponding first table cell
                    const firstParentRow = selectedCellData.attributes.get("data-FirstParentRow");
                    if (firstParentRow == null){
                        break;
                    }
                    var firstParentCol = columnLabel;
                    if (!grammar.terminals.has(firstParentCol)){
                        // Follow() column, first table parent cell is the epsilon column
                        firstParentCol = epsilon;
                    }
                    firstTable.setCellColor(firstParentRow,firstParentCol, HTMLColors.disableColor);
                    firstTable.setCellEnable(firstParentRow,firstParentCol, false);
                    // Remove it from the solving follow set and add it to grammar follow set
                    this.solvingFollowSet.delete(columnLabel);
                    var currentFollowSet = grammar.followSets.get(rowLabel);
                    if (currentFollowSet == null){
                        currentFollowSet = new Set();
                    }
                    currentFollowSet.add(columnLabel);
                    // Check if we are done with the current selection
                    if (this.solvingFollowSet.size == 0){
                        // Clear the selected cell
                        if (this.selectedCell == null){
                            break;
                        }
                        var currentSelectedCell = followTable.getCell(this.selectedCell.rowLabel, this.selectedCell.columnLabel)
                        if (currentSelectedCell == null){
                            break;
                        }
                        currentSelectedCell.color = HTMLColors.disableColor;
                        currentSelectedCell.data = emptyCell;
                        currentSelectedCell.enabled = false;
                        currentSelectedCell.attributes.delete("data-FirstParentRow");
                        // Remove the First() from the follow set
                        currentFollowSet.delete(`First(${firstParentRow})`);
                        this.selectedCell = null;
                    }
                }
                break;

            case Steps.FIND_FOLLOWS_COMPUTED_FOLLOWS:
                // Check if this is a parent cell or child cell
                if (selectedCellData.attributes.has('data-ParentCell')) {
                    if (this.selectedCell != null){
                        // Clear out any already selected cell
                        for( const oldColumn of this.solvingFollowSet.values()){
                            this.setCellEnable(this.selectedCell.rowLabel, oldColumn, false);
                            this.setCellColor(this.selectedCell.rowLabel, oldColumn, HTMLColors.disableColor);
                        }
                        this.solvingFollowSet.clear();
                    }
                    this.selectedCell = {rowLabel, columnLabel};
                    // Get the row that corresponds to this Follow() value
                    const followValueRowKey = extractRowKey(columnLabel);
                    if (followValueRowKey == null){
                        console.error("Column Symbol could not be found!");
                        return;
                    }
                    // Check for a Row that follows itself
                    if (followValueRowKey == rowLabel){
                        // Row that follows itself, Effectively already solved
                            setInstructionValue(
                                `A Row that Follows itself is already solved.`
                            );
                            // Clear the selected cell
                            this.selectedCell == null;
                            var currentSelectedCell = followTable.getCell(this.selectedCell.rowLabel, this.selectedCell.columnLabel)
                            if (currentSelectedCell == null){
                                break;
                            }
                            currentSelectedCell.color = HTMLColors.disableColor;
                            currentSelectedCell.data = emptyCell;
                            currentSelectedCell.enabled = false;
                            currentSelectedCell.attributes.delete("data-ParentCell");
                            break;
                    }
                    const followValueRow = this.tableData.get(followValueRowKey);
                    if (followValueRow == null){
                        break;
                    }
                    var allAlreadyFilled = true;
                    // Get the columns that are set in that row
                    for(const [followValueColumnKey, c] of followValueRow.entries()){
                        if (c.data != emptyCell){
                            // Check if that cell is already completed
                            var followSet = grammar.followSets.get(rowLabel);
                            if (followSet == null){
                                continue;
                            }
                            if (followSet.has(followValueColumnKey)){
                                // Already done, continue
                                continue;
                            }
                            // Highlight and Enable the corresponding cell
                            this.setCellColor(rowLabel, followValueColumnKey, HTMLColors.highlightColor);
                            this.setCellEnable(rowLabel, followValueColumnKey, true);
                            // this.setCellAttr(rowLabel, followValueColumnKey,CellAttr.prodRuleData, selectedCellData.data)
                            // Add it to the current solve set
                            this.solvingFollowSet.add(followValueColumnKey);
                            allAlreadyFilled = false;
                            setInstructionValue(
                                `Fill in the values in the ${rowLabel} row where they are also set in the ${followValueRowKey} row`
                            );
                        }
                    }

                    if (allAlreadyFilled == true){
                        // All the values that processing this follow would fill
                        // already are so just continue.
                        setInstructionValue(
                            "Select a Follow table cell with a Follow() column to simplify."
                        );
                        // Clear the selected cell
                        this.selectedCell == null;
                        var currentSelectedCell = followTable.getCell(this.selectedCell.rowLabel, this.selectedCell.columnLabel)
                        if (currentSelectedCell == null){
                            break;
                        }
                        currentSelectedCell.color = HTMLColors.disableColor;
                        currentSelectedCell.data = emptyCell;
                        currentSelectedCell.enabled = false;
                        currentSelectedCell.attributes.delete("data-ParentCell");
                    }

                }
                // Must be a child cell
                else {
                    // Get the value that needs to be placed in this cell
                    // Disable, Color, and place the prod number in the cell
                    followTable.setCellValue(rowLabel,columnLabel, 'X');
                    followTable.setCellColor(rowLabel, columnLabel, HTMLColors.disableColor);
                    followTable.setCellEnable(rowLabel,columnLabel, false);

                    // Remove it from the solving follow set and add it to grammar follow set
                    this.solvingFollowSet.delete(columnLabel);
                    var currentFollowSet = grammar.followSets.get(rowLabel);
                    if (currentFollowSet == null){
                        currentFollowSet = new Set();
                    }
                    currentFollowSet.add(columnLabel);
                    // Check if we are done with the current selection
                    if (this.solvingFollowSet.size == 0){
                        // Clear the selected cell
                        if (this.selectedCell == null){
                            break;
                        }
                        var currentSelectedCell = followTable.getCell(this.selectedCell.rowLabel, this.selectedCell.columnLabel)
                        if (currentSelectedCell == null){
                            break;
                        }
                        currentSelectedCell.color = HTMLColors.disableColor;
                        currentSelectedCell.data = emptyCell;
                        currentSelectedCell.enabled = false;
                        currentSelectedCell.attributes.delete("data-ParentCell");
                        // Remove the Follow() from the follow set
                        currentFollowSet.delete(`Follow(${rowLabel})`);
                        this.selectedCell = null;
                        setInstructionValue (
                            "Select a Follow table cell with a Follow() column to simplify."
                        )
                    }
                }
                break;

            case Steps.PLACE_FOLLOW_EPSILON_NUMBERS:
                // Check if this is the nullable column
                if (columnLabel == nullableColumnKey){
                    // Disable all cells
                    this.disableAllCells();
                    this.colorAllCells(HTMLColors.disableColor);
                    // Set this ones color back to red
                    this.setCellColor(rowLabel, columnLabel, HTMLColors.errorColor);
                    // Enable and highlight all cells in this row that aren't empty
                    for (const currentColumn of this.columns.values()){
                        if (currentColumn == nullableColumnKey){
                            continue;
                        }
                        const child = this.getCell(rowLabel, currentColumn);
                        if (child == null){
                            continue;
                        }
                        if (child.data != emptyCell){
                            // Highlight and enable
                            child.enabled = true;
                            child.color = HTMLColors.highlightColor;
                        }
                    }
                    setInstructionValue(
                        "Now copy the production rule's number to every cell set in this row."
                    )
                }
                else {
                    // Child Cell, Update the value
                    const nullColumn = this.getCell(rowLabel, nullableColumnKey);
                    if (nullColumn == null){
                        break;
                    }
                    selectedCellData.data = nullColumn.data;
                    selectedCellData.color = HTMLColors.disableColor;
                    selectedCellData.enabled = false;
                    const rowData = followTable.tableData.get(rowLabel);
                    if (rowData == null){
                        break;
                    }
                    var rowComplete = true;
                    for (const [otherColumn, otherCell] of rowData.entries()){
                        if (otherCell.data == "X"){
                            rowComplete =false;
                            break;
                        }
                    }
                    if (rowComplete){
                        setInstructionValue("Good Now Select Another Nullable Row.")
                    }
                }
                break;

            case Steps.CREATE_FINAL_TABLE:
                if (this.selectedCell != null){
                    // Disable the corresponding first table cell
                    firstTable.setCellColor(this.selectedCell.rowLabel, this.selectedCell.rowLabel, HTMLColors.disableColor);
                    firstTable.setCellEnable(this.selectedCell.rowLabel, this.selectedCell.rowLabel, false);
                }
                this.selectedCell = {rowLabel: rowLabel, columnLabel: columnLabel}
                // Select the corresponding first table cell
                const firstTableCell = firstTable.getCell(rowLabel, columnLabel);
                if (firstTableCell == null){
                    console.error("Could not get first table cell!")
                    break;
                }
                // Enable it
                firstTableCell.color = HTMLColors.highlightColor;
                firstTableCell.enabled = true;
                // Render first table
                firstTable.render();
                setInstructionValue("Now place this cell in the matching cell in the First Table.")

                break;

            default:
                break;
        }
    this.render();
    checkProgress();
    }

    ruleRowCallback(rowId: number) {
        const selectedProductionCells = selectedProductionFollowCells.get(rowId);
        if (selectedProductionCells == null){
            return;
        }
        if (selectedProductionCells.size == 0){
            setErrorValue("The selected production does not use this rule! Try again.");
        }
        else {
            setInstructionValue("Now select a value in the follow table that corresponds with this rule.")
            this.selectedRule = rowId;
            followTable.render();
        }
    }
}

// Check the progress of the current step, advancing if necessary
function checkProgress(delayInstruction: boolean = true){
    if (errorState == true){
        return;
    }
    switch (currentStep) {
        case Steps.ENTER_EPSILON:
            // Check that each production that produces epsilon has its first table
            // cell filled
            var done = true;
            for (var i = 0; i < productionTable.productions.length; i++){
                var prod = productionTable.productions[i];
                // Check if the production should produce epsilon
                if (prod.rule.right[0] == epsilon){
                    var cell = firstTable.getCell(prod.rule.left, epsilon);
                    // Check that its has been placed in the first table
                    if (cell != null){
                        if (cell?.data != prod.idx.toString()){
                            // Not complete yet
                            done = false;
                            break;
                        }
                    }
                }
            }

            // Check if done
            if (done == true){
                // Move on to the next step
                currentStep = Steps.ENTER_EPSILON_FROM_EPSILON;
                if (productionTable.selectedProduction != null) {
                    productionTable.setProductionRowEnable(productionTable.selectedProduction, false);
                }
                setInstructionValue(
                    "Correct. Now choose a production rule that can produce epsilon indirectly."
                );
                checkProgress();

            } else {
                // Keep going
                if (productionTable.selectedProduction != null) {
                    productionTable.setProductionRowEnable(productionTable.selectedProduction, false);
                }
                if (first_pass == true){
                    setInstructionValue("Select a production from the Production Table that can produce epsilon directly.")
                    first_pass = false;
                }
                else{
                    setInstructionValue("Correct, Now select another production that can produce epsilon directly.")
                }
            }
            break;

        case Steps.ENTER_EPSILON_FROM_EPSILON:
            var done = true;
            for (var i = 0; i < productionTable.productions.length; i++){
                var prod = productionTable.productions[i];

                // Check if the production should produce epsilon indirectly
                var indirectlyEpsilon = true;
                for (var j = 0 ; j < prod.rule.right.length; j++){
                    var indirectEpsilonCol = firstTable.getCell(prod.rule.right[j], epsilon);
                    if (indirectEpsilonCol != null){
                        // Check if the value is set
                        if (indirectEpsilonCol.data != emptyCell) {
                            // Current symbol can resolve to epsilon.
                            continue;
                        }
                    }
                    // Any other case, its not indirectly epsilon
                    indirectlyEpsilon = false;
                    break;
                }
                // Check if this was indirectly epsilon
                if (indirectlyEpsilon == true){
                    // Check that this production indicates that it can also
                    // be epsilon
                    var current_cell = firstTable.getCell(prod.rule.left, epsilon);

                    if (current_cell?.data == emptyCell){
                        // Not Done
                        done = false;
                        break;
                    }
                }
            }
            // Check if done
            if (done == true){
                // Move on to the next step
                currentStep = Steps.FIND_FIRSTS;
                if (productionTable.selectedProduction != null) {
                    productionTable.setProductionRowEnable(productionTable.selectedProduction, true);
                }
                setInstructionValue(
                    "Correct. Now choose a production rule and begin finding the First Values."
                );
                // Precalculate the first values of the production rules
                for (var i = 0; i< productionTable.productions.length; i++){
                    const prod = productionTable.productions[i];
                    // Walk through the right side
                    var firstSet = new Set(grammar.firstSets.get(prod.rule.left));
                    for (var j = 0; j< prod.rule.right.length; j++){
                        var currentSymbol = prod.rule.right[j];
                        // Check if its a non-terminal
                        if (grammar.terminals.has(currentSymbol) || currentSymbol == epsilon){
                            // Terminal, add it to the first set and move on
                            firstSet?.add(currentSymbol);
                            break;
                        }
                        else {
                            // Non terminal found, Check if it is nullable
                            // var childCell = getTableCell(firstTableID, currentSymbol, epsilon);
                            var childCell = firstTable.getCell(currentSymbol, epsilon);
                            if (childCell?.data != emptyCell){
                                // Nullable, Add to first set and continue through the production
                                firstSet?.add(`First(${currentSymbol})`);
                            }
                            else {
                                // Not Nullable, Add to first set and and stop
                                firstSet?.add(`First(${currentSymbol})`);
                                break;
                            }
                        }
                    }
                    grammar.firstSets.set(prod.rule.left, firstSet);
                    checkProgress();

                }
            } else {
                if (productionTable.selectedProduction != null) {
                    productionTable.setProductionRowEnable(productionTable.selectedProduction, true);
                }
                setInstructionValue("Correct, Now select another production that can indirectly produce epsilon.");
            }
            
            break;

        case Steps.FIND_FIRSTS:
            var allProdsComplete = true;
            for (var j = 0; j < productionTable.productions.length; j++){
                var prod = productionTable.productions[j];
                var prodComplete = true;
                // Walk through production and check if all of its firsts are placed
                for (var i = 0; i < prod.rule.right.length; i++ ){
                    var currentSymbol = prod.rule.right[i];
                    if (grammar.terminals.has(currentSymbol)){
                        var cell = firstTable.getCell(prod.rule.left, currentSymbol);
                        // var cell = getTableCell(
                        //     firstTableID,
                        //     prod.rule.left,
                        //     currentSymbol
                        // );
                        if (cell?.data != emptyCell){
                            // Production complete
                            break;
                        }
                        else {
                            prodComplete=false;
                            break;
                        }
                    }
                    else {
                        var correctColumn = `First(${currentSymbol})`;
                        var cell = firstTable.getCell(prod.rule.left, correctColumn);

                        if (cell?.data == emptyCell) {
                            prodComplete=false;
                            break;
                        }
                        else {
                            // Only continue if the symbol is nullable
                            var epsilonCell = firstTable.getCell(currentSymbol, epsilon);
                            if (epsilonCell?.data != emptyCell){
                                // Is nullable, Continue
                                continue;
                            }
                            else {
                                // Done
                                break
                            }
                        }
                    }
                }
                if (prodComplete){
                    // Only print this message if the current production being
                    // Checked is the selected production
                    if (j == productionTable.selectedProduction){
                        productionTable.setProductionRowEnable(j,false);
                        setErrorValue("");
                        setInstructionValue("Good Job. Now select another production.");
                    }
                }
                else {
                    allProdsComplete = false;
                }
            }
            if (allProdsComplete){
                console.log("Step: Find Firsts complete.")
                setInstructionValue("Good Job, Now Lets backfill the First() values in the table.");
                // Prepare the first table for the next step
                // First do a pass of the grammar first sets to see what can be
                // solved in a single pass
                processFirstSets();
                // Disable all the cells in the first table
                firstTable.colorAllCells(HTMLColors.disableColor);
                firstTable.disableAllCells();
                // Now update the step and run another pass of check progress
                currentStep = Steps.FIND_FIRSTS_COMPUTED
                checkProgress()
            }
            break;

        case Steps.FIND_FIRSTS_COMPUTED:
            // Start by finding what First() values still need to be solved in the
            // first table, Do this by checking all the row, col combinations
            // of the table
            var needSolvePass = true;
            for (const rowSymbol of grammar.nonTerminals.values()){
                // Skip any rows that cannot currently be solved
                if (!grammar.solvedFirstSets.has(rowSymbol)){
                    continue;
                }
                for (const colSymbol of grammar.nonTerminals.values()) {
                    const cell = firstTable.getCell(
                        rowSymbol,
                        `First(${colSymbol})`
                    )
                    if (cell == null){
                        continue;
                    }
                    // If this cell has a value set then it still needs to be
                    // solved.
                    if (cell.data != emptyCell){
                        // Now check if this cell can be solved this cycle by
                        // referencing the grammars firstSets
                        if (grammar.solvedFirstSets.has(rowSymbol)){
                            // Check if this has already been solved by another
                            // First() cell being solved (Due to implicit epsilon)
                            var notCompleted = false;
                            var currentFirstSet = grammar.firstSets.get(rowSymbol) as Set<string>;
                            for (var childSymbol of currentFirstSet.values()){
                                var symbolCell = firstTable.getCell(rowSymbol, childSymbol) as CellData;
                                if (symbolCell.data == emptyCell){
                                    notCompleted = true;
                                    break;
                                }
                                else if(symbolCell.data != cell.data){
                                    console.log("Left Recursion Detected in check")
                                    notCompleted = true;
                                    break;
                                }
                                else if (symbolCell.color == HTMLColors.highlightColor){
                                    notCompleted = true;
                                    break;
                                }
                            }
                            if (notCompleted){
                                // It can be solved this cycle, Highlight red, enable
                                // the cell, Mark that we don't need another solve pass
                                cell.color = HTMLColors.errorColor;
                                cell.enabled = true;
                                // Mark this cell as one that needs to be simplified
                                cell.attributes.set(CellAttr.needsSimplified, "true");
                                firstTable.setCell(
                                    rowSymbol,
                                    `First(${colSymbol})`,
                                    cell
                                );
                                needSolvePass = false;
                            }
                            else{
                                // Cell was already completed by another cell filling
                                // in all its first values
                                // It can be solved this cycle, Highlight red, enable
                                // the cell, Mark that we don't need another solve pass
                                cell.color = HTMLColors.disableColor;
                                cell.enabled = false;
                                cell.data = emptyCell;
                                // Mark this cell as one that needs to be simplified
                                cell.attributes.delete(CellAttr.needsSimplified);
                                firstTable.setCell(
                                    rowSymbol,
                                    `First(${colSymbol})`,
                                    cell
                                );
                                continue;
                            }
                        }
                    }

                }
            }
            // render the table
            firstTable.render()
            // Check if we need a new solve pass
            if (needSolvePass){
                // Check if all the first values are solved
                if (grammar.solvedFirstSets.size == grammar.firstSets.size){
                    // All first values have been solved, so we are done with
                    // this step
                    currentStep = Steps.FIND_FOLLOWS;
                    prepForFollowSolve();
                    checkProgress();
                }
                else {
                    processFirstSets();
                }
                firstTable.render();
                // Check progress again
                checkProgress();
            }
            break;

        case Steps.FIND_FOLLOWS:
            // Check if a rule and production are selected
            if (followTable.selectedRule == null || productionTable.selectedProduction == null){
                // Rule hasn't been selected, move on
                break;
            }
            var selectedCells = selectedProductionFollowCells.get(followTable.selectedRule);
            if (selectedCells == null){
                break;
            }
            // Check if the selected rule was the last of the current type
            if (selectedCells.size == 0){
                // Unselect this rule
                followTable.selectedRule = null;
                setInstructionValue("Good, Now select another Rule from the Follow Rules table.")
            }
            var allRulesComplete = true;
            for (const [ruleId, ruleCells] of selectedProductionFollowCells){
                if (ruleId > 2){
                    continue;
                }
                if (ruleCells.size != 0){
                    followTable.rulesData[ruleId] = true;
                    allRulesComplete = false;
                }
                else {
                    // Disable that rule
                    followTable.rulesData[ruleId] = false;
                }
            }
            // Check if all the rules have been finished for this production
            if (allRulesComplete){
                // Disable selected Production and move on
                productionTable.setProductionRowEnable(productionTable.selectedProduction, false);
                setInstructionValue("Good, Now select another Production from the Production Table.")
            }
            // Check if all productions have been finished
            var done = true;
            for (const prod of productionTable.productions){
                if (prod.enabled){
                    done=false;
                    break;
                }
            }
            if (done){
                // Done with this step
                setInstructionValue(
                    "Good Job. Now we need to simplify the First columns in the follow table. Select a Follow table cell with a First() column to simplify."
                );
                currentStep = Steps.FIND_FOLLOWS_COMPUTED_FIRSTS;
                // Hide the rules table
                followTable.renderRules = false;
                // Disable all cells to start
                followTable.disableAllCells();
                followTable.colorAllCells(HTMLColors.disableColor);
                // Highlight all the cells in the First() columns, and enable them
                for (const c of grammar.nonTerminals.values()){
                    const columnKey = `First(${c})`
                    for (const rowKey of grammar.nonTerminals.values()){
                        var followCell = followTable.getCell(rowKey, columnKey);
                        if (followCell == null){
                            continue;
                        }
                        else if (followCell.data != emptyCell){
                            // Enable and highlight the cell
                            followCell.color = HTMLColors.errorColor;
                            followCell.enabled = true;
                            followCell.attributes.set("data-ParentCell", "true");
                            followTable.setCell(rowKey, columnKey, followCell);
                        }
                    }
                }
                checkProgress();
                break;
            }
            break;

        case Steps.FIND_FOLLOWS_COMPUTED_FIRSTS:
            // Check if we are already solving a First Column
            if (followTable.selectedCell != null ){
                // Already solving a First()
                    setInstructionValue(
                        "Select a highlighted cell in the First table to place in the Follow table."
                    )
            }
            // Check if all the First() values are solved
            else if (followTable.solvingFollowSet.size == 0) {
                // Just solved the First() column
                followTable.selectedCell = null;

                setInstructionValue("Select a Follow table cell with a First() column to simplify.");
            }
            var done = true;
            // Check if we have solved all the First Columns
            for (const c of grammar.nonTerminals.values()){
                const columnKey = `First(${c})`
                for (const rowKey of grammar.nonTerminals.values()){
                    var followCell = followTable.getCell(rowKey, columnKey);
                    if (followCell == null){
                        continue;
                    }
                    else if (followCell.data != emptyCell){
                        // Still Solving
                        done = false;
                    }
                }
            }
            if (done){
                // Move to next step
                currentStep = Steps.FIND_FOLLOWS_COMPUTED_FOLLOWS
                // Hide the First() columns
                for (const nonTerm of grammar.nonTerminals){
                    const column = `First(${nonTerm})`;
                    const idx = followTable.columns.indexOf(column);
                    if (idx < 0 ){
                        continue;
                    }
                    followTable.columns.splice(idx, 1);
                    for (const followColumn of followTable.tableData.values()){
                        followColumn.delete(column)
                    }
                }
                // Disable all cells to start
                followTable.disableAllCells();
                followTable.colorAllCells(HTMLColors.disableColor);
                // Highlight all the cells in the Follow() columns, and enable them
                for (const c of grammar.nonTerminals.values()){
                    const columnKey = `Follow(${c})`
                    for (const rowKey of grammar.nonTerminals.values()){
                        var followCell = followTable.getCell(rowKey, columnKey);
                        if (followCell == null){
                            continue;
                        }
                        else if (followCell.data != emptyCell){
                            // Enable and highlight the cell
                            followCell.color = HTMLColors.errorColor;
                            followCell.enabled = true;
                            followCell.attributes.set("data-ParentCell", "true");
                            followTable.setCell(rowKey, columnKey, followCell);
                        }
                    }
                }
                setInstructionValue (
                    "Select a Follow table cell with a Follow() column to simplify."
                )
                checkProgress();
            }
            break;

        case Steps.FIND_FOLLOWS_COMPUTED_FOLLOWS:
            // Check if we are already solving a Follow Column
            if (followTable.selectedCell != null ){
            }
            // Check if all the Follow() values are solved
            else if (followTable.solvingFollowSet.size == 0) {
                // Just solved the Follow() column
                followTable.disableAllCells();
                followTable.colorAllCells(HTMLColors.disableColor);
                // Highlight all the cells in the Follow() columns, and enable them
                for (const c of grammar.nonTerminals.values()){
                    const columnKey = `Follow(${c})`
                    for (const rowKey of grammar.nonTerminals.values()){
                        var followCell = followTable.getCell(rowKey, columnKey);
                        if (followCell == null){
                            continue;
                        }
                        else if (followCell.data != emptyCell){
                            // Enable and highlight the cell
                            followCell.color = HTMLColors.errorColor;
                            followCell.enabled = true;
                            followCell.attributes.set("data-ParentCell", "true");
                            followTable.setCell(rowKey, columnKey, followCell);
                        }
                    }
                }
                setInstructionValue (
                    "Select a Follow table cell with a Follow() column to simplify."
                )
                followTable.selectedCell = null;
            }
            var done = true;
            // Check if we have solved all the Follow Columns
            for (const c of grammar.nonTerminals.values()){
                const columnKey = `Follow(${c})`
                for (const rowKey of grammar.nonTerminals.values()){
                    var followCell = followTable.getCell(rowKey, columnKey);
                    if (followCell == null){
                        continue;
                    }
                    else if (followCell.data != emptyCell){
                        // Still Solving
                        done = false;
                    }
                }
            }
            if (done){
                // We have build the tables
                // Hide the Follow() columns
                for (const nonTerm of grammar.nonTerminals){
                    const column = `Follow(${nonTerm})`;
                    const idx = followTable.columns.indexOf(column);
                    if (idx < 0 ){
                        continue;
                    }
                    followTable.columns.splice(idx, 1);
                    for (const followColumn of followTable.tableData.values()){
                        followColumn.delete(column)
                    }
                }
                // Disable all cell
                followTable.disableAllCells();
                firstTable.disableAllCells();
                // Color them normally
                followTable.colorAllCells(HTMLColors.defaultColor);
                firstTable.colorAllCells(HTMLColors.defaultColor);

                // Mark as done
                currentStep = Steps.PLACE_FOLLOW_EPSILON_NUMBERS
                setInstructionValue(
                    [
                        "Good Job, The First and Follow tables are now complete! ",
                        "Now We will place the production rules # that are nullable ",
                        "in the follow table to see what follow table values we will need.",
                        " The Epsilon Column from the first table is what determines if a ",
                        "Production is nullable. It has been copied to the follow table for now. ",
                        "Select A highlighted Nullable cell to begin."
                    ].join('')
                )
                prepForFollowIdxPlacement();

            }
            break;

        case Steps.PLACE_FOLLOW_EPSILON_NUMBERS:
            // Verify that all Nullable rows have their indexes placed
            var done = true;
            for (const rowKey of followTable.rows.values()){
                // Check if this row is nullable
                const nullColumn = followTable.getCell(rowKey, nullableColumnKey);
                if (nullColumn == null){
                    continue;
                }
                if (nullColumn.data == emptyCell){
                    continue;
                }
                var rowComplete = true;
                // Check all the columns for the correct index
                for (const columnKey of followTable.columns.values()){
                    if (columnKey == nullableColumnKey){
                        continue;
                    }
                    const cellData = followTable.getCell(rowKey,columnKey);
                    if (cellData == null){
                        continue;
                    }
                    if (cellData.data == emptyCell){
                        continue;
                    }
                    if (cellData.data != nullColumn.data){
                        // Not Done
                        done = false;
                        rowComplete= false;
                    }
                }
                if (rowComplete){
                    // Disable the null column
                    nullColumn.color = HTMLColors.disableColor;
                    nullColumn.enabled = false;

                }
                else {
                    nullColumn.color = HTMLColors.errorColor;
                    nullColumn.enabled = true;
                }
            }
            if (done == true){
                // Update for next state
                currentStep = Steps.CREATE_FINAL_TABLE
                // Remove null column
                let index = followTable.columns.indexOf(nullableColumnKey);
                if (index > -1) {
                    followTable.columns.splice(index, 1);
                }
                setInstructionValue(
                    [
                        "Now we can build the Final Production Table. ",
                        "We will use the first table as our final production table. ",
                        "To create the Final Production Table, we need to fill the ",
                        "First table with the Follow Table Values. ",
                        "Select a Follow Table Value to begin. "
                    ].join('')
                )
                currentStep = Steps.CREATE_FINAL_TABLE
                prepForFinalTableBuild();
            }
            break;

        case Steps.CREATE_FINAL_TABLE:
            // Check if all the follow table cells have been placed
            var done = true;
            for (const [rowKey, columnMap] of followTable.tableData) {
                if (followTable.rows.indexOf(rowKey) == -1){
                    continue;
                }
                for (const columnKey of followTable.columns.values()) {
                    if (followTable.columns.indexOf(columnKey) == -1){
                        continue
                    }
                    const cellData = columnMap.get(columnKey);
                    if (cellData == null){
                        continue
                    }
                    if (cellData.enabled == true){
                        done = false;
                        break;
                    }
                }
            }
            if (done){
                currentStep = Steps.DONE;
                // Hide the follow table
                followTable.hidden = true
                // Update the first table name
                firstTable.tableHeaderStr = "Transition Table"
                // Remove epsilon column from first table
                let index = firstTable.columns.indexOf(epsilon);
                if (index > -1) {
                    firstTable.columns.splice(index, 1);
                }
                firstTable.colorAllCells(HTMLColors.defaultColor);
                setInstructionValue("The Transition Table is now complete.")

                // Fill the table with the actual production rules
                for (const [rowKey, columnMap] of firstTable.tableData) {
                    for (const columnKey of firstTable.columns.values()) {
                        const cellData = columnMap.get(columnKey);
                        if (cellData == null){
                            continue
                        }
                        if (cellData.data != emptyCell){
                            const prod = productionTable.productions[parseInt(cellData.data)]
                            cellData.data = `${prod.rule.left} ::= ${prod.rule.right.join("")}`
                        }
                    }
                }
            }
            break;

        default:
            break;
        }
    productionTable.render()
    firstTable.render()
    followTable.render()
}

// This function parses an array of strings, where each string is a production rule,
// into a structured Grammar object.
function createGrammar(input: string): Grammar| null {
    try {
    // Initialize an empty array for production rules.
    const rules: ProductionRule[] = [];
    // Initialize sets for terminals and non-terminals.
    const terminals = new Set<string>();
    const nonTerminals = new Set<string>();
    var firstSets = new Map();
    var followSets= new Map();
    // Split input string into lines
    var inputLines = input.trim().split(/(?:\r?\n)+/)
    // Add the starting rule
    const [left, right] = inputLines[0].split("::=").map((s) => s.trim());
    const productionStrings = [`S ::= ${left} $`].concat(inputLines);
    // Process each line of the grammar input.
    for (const line of productionStrings) {
        const [left, right] = line.split("::=").map((s) => s.trim());
        // The left-hand side is always a non-terminal.
        nonTerminals.add(left);
    }
    for (const line of productionStrings) {
        // Split the production rule by " ::=" and remove extra whitespace.
        const [left, right] = line.split("::=").map((s) => s.trim());
        // Split the right-hand side by the OR symbol ('|') to get alternative productions.
        // Each alternative represents a separate production rule.
        const alternatives = right.split("|").map(alt => alt.trim());

        // Process each alternative.
        for (const alt of alternatives) {
            // Split the alternative into individual symbols by spaces.
            // Filter out any empty strings that might occur due to extra whitespace.
            const rightSymbols = alt.split(" ").filter(sym => sym.length > 0);

            // Create a production rule object and add it to the rules array.
            rules.push({ left, right: rightSymbols });


            // Determine if each symbol on the right-hand side is a terminal or non-terminal.
            rightSymbols.forEach((symbol) => {
                console.log(`Right Symbol: ${symbol}`)
                // Skip for epsilon
                if (symbol == epsilon){
                    // Do nothing
                }

                else if (!(nonTerminals.has(symbol))) {
                    terminals.add(symbol);
                }
            });
        }

    }
    // Populate the first and follow sets
    nonTerminals.forEach((term) => {
        firstSets.set(term, new Set());
        followSets.set(term, new Set());
    })
    // Check for empty productions
    if (nonTerminals.size == 0){
        // No productions entered
        return null;
    }
    var solvedFirstSets = new Set<string>;
    // Return the structured grammar object with empty FIRST and FOLLOW sets.
    return {
        terminals,
        nonTerminals,
        rules,
        firstSets,
        followSets,
        solvedFirstSets
    };
    } catch (error) {
        console.error("Could not parse input Grammar!");
        return null;
    }
}

// Runs a single pass of the first sets backfilling algorithm to help track what
// cells can be backfilled in the FIRSTS_COMPUTED step
function processFirstSets(){
    // clear any colors and disable the cells
    firstTable.colorAllCells(HTMLColors.disableColor);
    firstTable.disableAllCells();
    var processedFirstSets = new Map<string, Set<string>>();
    for (const [key, value] of grammar.firstSets.entries()){
        // Create a copy of the first set to use to prevent changing it during
        // the loop
        var newFirstSet = new Set<string>();
        for (const symbol of value.values()){
            // Only select the non-terminal values
            if (grammar.terminals.has(symbol) || symbol == epsilon){
                // Copy the terminals to the new set
                newFirstSet.add(symbol);
                continue;
            }
            // Extract the symbol from the string 'First(symbol)'
            const rawSymbol = extractRowKey(symbol);
            if (rawSymbol == null){
                console.error("Column Symbol could not be found!");
                return;
            }
            // Pull the first set from the rawSymbol
            const childFirstSet = grammar.firstSets.get(rawSymbol);
            // Null check
            if (childFirstSet == null){
                continue;
            }
            // Add the child symbols to the new set
            for (const childSymbol of childFirstSet?.values()){
                // Check for self referential first sets
                if (childSymbol == `First(${key})`){
                    // Skip adding this
                    continue;
                }
                newFirstSet.add(childSymbol);
            }
        }
        // Update the original first set
        processedFirstSets.set(key, newFirstSet);
        // Check if this first set is solved
        var isSolved = true;
        for (const symbol of newFirstSet.values()){
            if (!(grammar.terminals.has(symbol) || (symbol == epsilon))){
                // Not Solved
                isSolved = false;
                break;
            }
        }
        // Mark solved as needed
        if (isSolved){
            grammar.solvedFirstSets.add(key);
        }
    }
    grammar.firstSets = processedFirstSets;
}

// Prepares for the follow table to be solved
function prepForFollowSolve(){
    // Un-hide the table
    followTable.setTableHidden(false);
    followTable.renderRules = true;
    // Enable all the rows in the production table that contain non-terminals,
    // Disabling others
    for (var i = 0; i < productionTable.productions.length; i++){
        const prod = productionTable.productions[i];
        var enableRow = false;
        for (const symbol of prod.rule.right.values()){
            if (grammar.nonTerminals.has(symbol)){
                enableRow = true;
                break;
            }
        }
        productionTable.setProductionRowEnable(i, enableRow);
    }
    // Disable first table
    firstTable.disableAllCells();
    firstTable.colorAllCells(HTMLColors.disableColor);
    // Remove the un-needed rows in the first table
    for (const nonTerm of grammar.nonTerminals){
        const column = `First(${nonTerm})`;
        const idx = firstTable.columns.indexOf(column);
        if (idx < 0 ){
            continue;
        }
        firstTable.columns.splice(idx, 1);
        for (const firstColumn of firstTable.tableData.values()){
            firstColumn.delete(column)
        }
    }
    // Render tables
    firstTable.render();
    followTable.render();
    productionTable.render();
    setInstructionValue(
        "Now we can begin to solve the Follow Table. Select a production that contains a non-terminal in its right hand side to begin."
    )
}

// Prepare the follow table for solving the nullable sets after it has been
// completed
function prepForFollowIdxPlacement(){
    followTable.columns.push(nullableColumnKey);
    // Render to create new column
    followTable.render();
    followTable.disableAllCells();
    followTable.colorAllCells(HTMLColors.disableColor);
    // Fill the data from the first table
    for (const [rowKey, columnMap] of firstTable.tableData) {
        const cellData = columnMap.get(epsilon)
        var data = cellData?.data as string;
        followTable.setCellValue(rowKey, nullableColumnKey, data)
        // Add style override
        const cellStyle = {
            "border-left": "3px solid black",
            "border-right": "3px solid black",
            "border-collapse": "collapse"
        }
        followTable.setCellAttr(rowKey, nullableColumnKey, CellAttr.styleOverride, JSON.stringify(cellStyle))
        if (data != emptyCell){
            // Row will need to be filled
            followTable.setCellColor(rowKey,nullableColumnKey, HTMLColors.errorColor);
            followTable.setCellEnable(rowKey,nullableColumnKey, true);
        }
        else {
            followTable.setCellColor(rowKey,nullableColumnKey, HTMLColors.disableColor);
            followTable.setCellEnable(rowKey,nullableColumnKey, false);
        }
        console.log(rowKey, columnMap.get(epsilon));
    }
    followTable.render()

}

// Prepare to place the final values in the first table
function prepForFinalTableBuild(){
    // Render follow to flush values
    followTable.render();
    // Disable all cells in both tables
    firstTable.disableAllCells();
    firstTable.colorAllCells(HTMLColors.disableColor);
    followTable.disableAllCells();
    followTable.colorAllCells(HTMLColors.disableColor);
    // Enable any cells in the follow table that have a value set
    var removeRows: string[] = []
    var rowNeeded = false;

    for (const [rowKey, columnMap] of followTable.tableData) {
        rowNeeded = false;
        for (const columnKey of followTable.columns.values()) {
            const cellData = columnMap.get(columnKey);
            if (cellData == null){
                continue
            }
            if (cellData.data == "X"){
                continue
            }
            else if (cellData.data != emptyCell){
                rowNeeded = true;
                cellData.color = HTMLColors.errorColor;
                cellData.enabled = true;
            }
        }
        if (rowNeeded = false){
            removeRows.push(rowKey);
        }
    }
    // Remove un-needed rows
    followTable.rows = followTable.rows.filter(item => !removeRows.includes(item));
    followTable.render();
    firstTable.render();
}


// Start the Parser and build the starting tables, OnClick function for the
// grammar input box "=>" button
function startParser(){
    // Collect and use the input from the user
    resetError();
    let inputBox = document.getElementById(grammarInputBox) as HTMLTextAreaElement;
    if (inputBox == null){
        // Could not acquire the input box element
        return null;
    }
    grammar = createGrammar(inputBox.value) as Grammar;
    if (grammar == null){
        setInstructionValue("");
        setErrorValue(
            "Could Not Parse the inputted grammar. Please check for typos and try again!"
        );
    }
    else {
        currentStep = Steps.ENTER_EPSILON;
        productionTable = new ProductionTable(grammarProductionColumn, grammar);
        firstTable = new FirstTable(grammar);
        followTable = new FollowTable(grammar);
        // Hide the follow table for now
        followTable.setTableHidden(true);
        followTable.render()
        setInstructionValue("Select a production that can produce epsilon directly.");
        setErrorValue("");
        first_pass = true;
        checkProgress();
    }
}

// Set up for the page
function setup(){
    let inputBox = document.getElementById(grammarInputBox) as HTMLTextAreaElement;
    if (inputBox != null){
        console.log(defaultGrammar)
        inputBox.innerHTML = defaultGrammar;
    }
    currentStep = Steps.ENTER_GRAMMAR;
    setInstructionValue("Enter a grammar and hit the => to start, Or select Random.")
}

function generateRandomCharacter(alphabet: string): string {
    const randomIndex = Math.floor(Math.random() * alphabet.length * alphabet.length) % alphabet.length;
    return alphabet[randomIndex];
}

function getRandomProduction(L: string, nonTerminals:string = sampleNonTerminals, maxLen: number = 10): string {
    const length = Math.floor(Math.random() * 100) % maxLen + 1;
    var availNonTerms = nonTerminals.split(L).join("");
    var RHS = new Array<string>;
    if (Math.random() > 0.4){
        // Just other non terms
        for (var i = 0; i < length; i++) {
                // Non-Terminal
                const randChar = generateRandomCharacter(availNonTerms)
                availNonTerms = availNonTerms.split(randChar).join("")
                RHS.push(randChar);
        }
    }
    else {
        for (var i = 0; i < length; i++) {
            if (Math.random() > 0.9){
                // Non-Terminal
                const randChar = generateRandomCharacter(availNonTerms)
                availNonTerms = availNonTerms.split(randChar).join("")
                RHS.push(randChar);
            }
            else {
                // Terminal
                RHS.push(generateRandomCharacter(sampleTerminals));
            }
        }
    }

    return `${L} ::= ${RHS.join(" ")}`;
}

// Random Grammar Button
function randomGrammar(){
    console.log("Creating Random Productions...")
    var numberOfNonTerminals = Math.floor((Math.random() * 10) ) % 5;
    if (numberOfNonTerminals < 3){
        numberOfNonTerminals = numberOfNonTerminals +3;
    }
    var possibleNonTerms = sampleNonTerminals;
    var nonTerminals = ""
    for (var i=0 ; i < numberOfNonTerminals; i++){
        const randChar = generateRandomCharacter(possibleNonTerms)
        nonTerminals = nonTerminals + randChar;
        possibleNonTerms = possibleNonTerms.split(randChar).join("");
    }
    console.log(`# ${numberOfNonTerminals} NonTerms: ${nonTerminals}`)
    var productions = new Array<string>();
    var chance = Math.random();
    for (var i=0; i < nonTerminals.length;i ++){
        var LHS = nonTerminals[i];

        var repeat = true;
        if ((nonTerminals.length - 3) - i < 0){
            productions.push(`${LHS} ::= e`)
        }
        while (repeat){
            var prod = getRandomProduction(LHS, nonTerminals);
            console.log(prod);
            productions.push(prod);
            if (Math.random() < chance) {
                chance = chance / 2;
                console.log(`Creating additional production for nonTerm: ${LHS}`)
                continue
            }
            else{
                repeat = false;
            }
        }
    }
    var joinedProductions = productions.join("\n")
    console.log("Productions: ")
    console.log(joinedProductions)
    let inputBox = document.getElementById(grammarInputBox) as HTMLTextAreaElement;
    if (inputBox != null){
        inputBox.innerHTML = joinedProductions;
    }
}

const sampleTerminals = '+-()'
const sampleNonTerminals = 'ABCDEFGHIJKLMNOPQRTUVWXYZ'
