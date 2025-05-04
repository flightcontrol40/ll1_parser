"use strict";
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
var epsilon = "e";
var assignmentSymbol = "::=";
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
const messageTableID = "Instructions";
const messageParent = "MessageTable";
const headingTable = "Table_1";
const assignmentSymId = "assignmentSym";
const epsilonSymId = "epsilonSym";
const emptyCell = ".";
const noButtonId = "noButton";
const yesButtonId = "yesButton";
const nullableColumnKey = "Nullable";
const leftRecursionErrorStr = "Left Recursion Detected, Cannot Continue! The Grammar is not LL(1) Parsable!";
const unparsableGrammarErrorStr = "The Grammar is not LL(1) Parsable!";
const noButton = document.getElementById(noButtonId);
const yesButton = document.getElementById(yesButtonId);
const defaultGrammar = [
    "D ::= R",
    "R ::= B C",
    "B ::= +",
    "B ::= e",
    "C ::= -",
    "C ::= e",
].join("\n");
const defaultGrammar4 = [
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
const defaultGrammar3 = [
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
const defaultGrammar2 = [
    "A ::= B",
    "B ::= C",
    "C ::= A",
    "C ::= -",
].join("\n");
const defaultGrammar5 = [
    "A ::= & C | !",
    "B ::= * A",
    "C ::= % B | e",
].join("\n");
// Colors to use for tables
var HTMLColors;
(function (HTMLColors) {
    HTMLColors["defaultColor"] = "white";
    HTMLColors["disableColor"] = "gray";
    HTMLColors["highlightColor"] = "yellow";
    HTMLColors["darkHighlightColor"] = "#ffcc00";
    HTMLColors["softGreyColor"] = "#e4e3e3";
    HTMLColors["errorColor"] = "red";
    HTMLColors["textColor"] = "black";
    HTMLColors["epsilonColor"] = "#dbdbdb";
})(HTMLColors || (HTMLColors = {}));
// Cell State attributes
var CellAttr;
(function (CellAttr) {
    CellAttr["needsSimplified"] = "data-NeedsSimplified";
    CellAttr["needsFilled"] = "data-NeedsFilled";
    CellAttr["parentCellCol"] = "data-ParentCellCol";
    CellAttr["childCellCol"] = "data-ChildCellCol";
    CellAttr["prodRuleData"] = "data-ProductionRuleData";
    CellAttr["styleOverride"] = "data-StyleOverride";
    CellAttr["copyCellKey"] = "data-CopyCellKey";
})(CellAttr || (CellAttr = {}));
// Steps enum
var Steps;
(function (Steps) {
    Steps[Steps["INVALID"] = -1] = "INVALID";
    Steps[Steps["ENTER_GRAMMAR"] = 0] = "ENTER_GRAMMAR";
    Steps[Steps["ENTER_EPSILON"] = 1] = "ENTER_EPSILON";
    Steps[Steps["ENTER_EPSILON_FROM_EPSILON"] = 2] = "ENTER_EPSILON_FROM_EPSILON";
    Steps[Steps["FIND_FIRSTS"] = 3] = "FIND_FIRSTS";
    Steps[Steps["FIND_FIRSTS_COMPUTED"] = 4] = "FIND_FIRSTS_COMPUTED";
    Steps[Steps["FOLLOW_NEEDED"] = 5] = "FOLLOW_NEEDED";
    Steps[Steps["FIND_FOLLOWS"] = 6] = "FIND_FOLLOWS";
    Steps[Steps["FIND_FOLLOWS_COMPUTED_FIRSTS"] = 7] = "FIND_FOLLOWS_COMPUTED_FIRSTS";
    Steps[Steps["FIND_FOLLOWS_COMPUTED_FOLLOWS"] = 8] = "FIND_FOLLOWS_COMPUTED_FOLLOWS";
    Steps[Steps["PLACE_FOLLOW_EPSILON_NUMBERS"] = 9] = "PLACE_FOLLOW_EPSILON_NUMBERS";
    Steps[Steps["CREATE_FINAL_TABLE"] = 10] = "CREATE_FINAL_TABLE";
    Steps[Steps["DONE"] = 11] = "DONE";
})(Steps || (Steps = {}));
;
var FollowRuleType;
(function (FollowRuleType) {
    FollowRuleType[FollowRuleType["TERMINAL_FOLLOWS"] = 0] = "TERMINAL_FOLLOWS";
    FollowRuleType[FollowRuleType["NON_TERMINAL_FOLLOWS"] = 1] = "NON_TERMINAL_FOLLOWS";
    FollowRuleType[FollowRuleType["END_OF_PRODUCTION"] = 2] = "END_OF_PRODUCTION";
    FollowRuleType[FollowRuleType["FIRST_SIMPLIFY"] = 3] = "FIRST_SIMPLIFY";
    FollowRuleType[FollowRuleType["FOLLOW_SIMPLIFY"] = 3] = "FOLLOW_SIMPLIFY";
})(FollowRuleType || (FollowRuleType = {}));
////////////////////////////////////////////////////////////////////////////////
// Global Variables
////////////////////////////////////////////////////////////////////////////////
var grammar;
var currentStep = Steps.ENTER_GRAMMAR;
var productionTable;
var firstTable;
var followTable;
var instructionString = '';
var errorString = '';
var errorState = false;
var selectedProductionFollowCells = new Map([
    [FollowRuleType.TERMINAL_FOLLOWS, new Set()],
    [FollowRuleType.NON_TERMINAL_FOLLOWS, new Set()],
    [FollowRuleType.END_OF_PRODUCTION, new Set()],
    [FollowRuleType.FIRST_SIMPLIFY, new Set()],
    [FollowRuleType.FOLLOW_SIMPLIFY, new Set()],
]);
var FollowRules = new Map([
    [FollowRuleType.TERMINAL_FOLLOWS, "A non-terminal followed by a terminal."],
    [FollowRuleType.NON_TERMINAL_FOLLOWS, "A non-terminal followed by a non-terminal."],
    [FollowRuleType.END_OF_PRODUCTION, "A non-terminal at the end of a production."],
]);
var first_pass = true;
var input_error_str = "";
////////////////////////////////////////////////////////////////////////////////
//  HTML Helper Functions
////////////////////////////////////////////////////////////////////////////////
function deleteMyTable(myTableId) {
    var element = document.getElementById(myTableId);
    if (element != null)
        element.parentNode.removeChild(element);
}
// Set the string in the instruction field
function setInstructionValue(value, clear = true) {
    var instructions = document.getElementById(messageTableID);
    instructionString = value;
    if (clear) {
        errorString = '';
    }
    instructions.textContent = [instructionString, errorString].join("\n");
}
// Set an Error value in the instruction field.
function setErrorValue(value) {
    var instructions = document.getElementById(messageTableID);
    errorString = value;
    instructions.textContent = [instructionString, errorString].join("\n");
}
// Get the non-terminal row key from a string of type 'First(<non-term>)' or
// 'Follow(<non-term>)' 
function extractRowKey(value) {
    var _a;
    if (value == null) {
        return null;
    }
    const regex = /(?:(?:First|Follow)\((?<row>.*)\))/;
    const found = value.match(regex);
    if (found != null) {
        const row = (_a = found.groups) === null || _a === void 0 ? void 0 : _a.row;
        if (row == null) {
            return null;
        }
        return row;
    }
    return null;
}
// Represents the current state of the Production Table
class ProductionTable {
    constructor(parentID, grammar) {
        this.tableID = productionTableID;
        this.productions = new Array();
        for (const [idx, rule] of grammar.rules.entries()) {
            this.productions.push({
                idx: idx,
                rule: rule,
                enabled: true,
                color: HTMLColors.defaultColor
            });
        }
        this.selectedProduction = null;
        this.table = document.createElement("TABLE");
        this.parentID = parentID;
        this.render();
    }
    _setRowCallback(row, rowIdx, table) {
        row.onclick = function () { table.buttonCallback(rowIdx); };
        row.style.cursor = "pointer";
    }
    render() {
        // Remove old table
        deleteMyTable(this.tableID);
        // Create a new one based on the current state
        this.table = document.createElement("TABLE");
        this.table.setAttribute("id", this.tableID);
        this.table.style.float = "right";
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
        for (var y = 0; y < this.productions.length; y++) {
            var prod = this.productions[y];
            var newRow = document.createElement("TR");
            if (prod.enabled) {
                this._setRowCallback(newRow, y, this);
            }
            //     this.ButtonCallback(prod.idx);
            // }};
            newRow.setAttribute("id", prod.rule.left + ` ${assignmentSymbol} ` + prod.rule.right.join(""));
            newRow.style.border = "1px solid black";
            // Create index cell
            var idxCell = document.createElement("TD");
            idxCell.style.width = "24px";
            idxCell.style.border = "1px solid black";
            idxCell.style.color = "black";
            idxCell.style.backgroundColor = HTMLColors.softGreyColor;
            idxCell.textContent = y.toString();
            newRow.appendChild(idxCell);
            // Create Cell
            var cell = document.createElement("TD");
            newRow.appendChild(cell);
            cell.style.width = "350px";
            cell.style.border = "1px solid black";
            cell.style.color = "black";
            // Add production rule
            cell.textContent = prod.rule.left + ` ${assignmentSymbol} ` + prod.rule.right.join("");
            // Set the row color
            newRow.style.backgroundColor = prod.color;
            this.table.appendChild(newRow);
        }
        // Add the created table back
        var parent = document.getElementById(this.parentID);
        parent === null || parent === void 0 ? void 0 : parent.appendChild(this.table);
    }
    disableAllRows() {
        for (var y = 0; y < this.productions.length; y++) {
            this.setProductionRowEnable(y, false);
        }
    }
    setProductionRowEnable(row, enable) {
        this.productions[row].enabled = enable;
        if (enable == true) {
            this.productions[row].color = HTMLColors.defaultColor;
            this.productions[row].enabled = true;
        }
        else {
            this.productions[row].enabled = false;
            this.productions[row].color = HTMLColors.disableColor;
        }
        if (this.selectedProduction == this.productions[row].idx) {
            this.selectedProduction = null;
        }
    }
    selectProductionRow(row) {
        if (!this.productions[row].enabled) {
            this.selectedProduction = null;
            return false;
        }
        if (this.selectedProduction != null) {
            const oldSelection = this.productions[this.selectedProduction];
            if (oldSelection.enabled) {
                oldSelection.color = HTMLColors.defaultColor;
            }
        }
        this.selectedProduction = row;
        this.productions[row].color = HTMLColors.highlightColor;
        console.log(`Selected Production Table Row: ${row} `);
        return true;
    }
    buttonCallback(row) {
        var _a, _b, _c;
        if (errorState == true) {
            return null;
        }
        const prod = this.productions[row];
        switch (currentStep) {
            // Check if this rule directly produces epsilon
            case Steps.ENTER_EPSILON:
                if (prod.rule.right[0] == epsilon) {
                    // This is a valid selection
                    this.selectProductionRow(row);
                    setInstructionValue("Now select the cell in the first table that corresponds with this non-terminal producing epsilon. ");
                }
                else {
                    setInstructionValue("The Selected production does not directly produce epsilon! Try again.");
                    // Reset the selected row
                    if (this.selectedProduction != null) {
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
                for (var i = 0; i < prod.rule.right.length; i++) {
                    var indirectEpsilonCol = firstTable.getCell(prod.rule.right[i], epsilon);
                    if (indirectEpsilonCol != null) {
                        // Check if the value is set
                        if (indirectEpsilonCol.data != emptyCell) {
                            // This letter can produce epsilon check the next
                            continue;
                        }
                        else {
                            indirectlyEpsilon = false;
                            // Not indirectly producible for now, but could be in the future
                            setInstructionValue("The Selected production rule does not indirectly produce epsilon currently! Try again.");
                            // Reset the selected row
                            if (this.selectedProduction != null) {
                                this.productions[this.selectedProduction].color = HTMLColors.defaultColor;
                                this.selectedProduction = null;
                            }
                        }
                    }
                    else {
                        indirectlyEpsilon = false;
                        // Not producible
                        setInstructionValue("The Selected production rule does not indirectly produce epsilon! Try again.");
                        // Reset the selected row
                        if (this.selectedProduction != null) {
                            this.productions[this.selectedProduction].color = HTMLColors.defaultColor;
                            this.selectedProduction = null;
                        }
                    }
                }
                if (indirectlyEpsilon == true) {
                    // Can be produced indirectly
                    this.selectProductionRow(row);
                    setInstructionValue("Now select the cell in the first table that corresponds with the rule producing epsilon.");
                }
                break;
            // Find the first value for this production
            case Steps.FIND_FIRSTS:
                this.selectProductionRow(row);
                // Check where this production rule should be placed
                var instructions = new Array();
                for (var i = 0; i < prod.rule.right.length; i++) {
                    if (grammar.terminals.has(prod.rule.right[i])) {
                        instructions.push(`First(${prod.rule.left}) ${assignmentSymbol} '${prod.rule.right[i]}'. So put a ${row} at the intersection of ${prod.rule.left} and ${prod.rule.right[i]} in the First Table.`);
                        break;
                    }
                    else {
                        instructions.push(`First(${prod.rule.left}) ${assignmentSymbol} 'First(${prod.rule.right[i]})'. So put a ${row} at the intersection of ${prod.rule.left} and First(${prod.rule.right[i]}) in the First Table.`);
                        // Check if this is nullable
                        var epsilonCell = firstTable.getCell(prod.rule.right[i], epsilon);
                        if (epsilonCell == null) {
                            break;
                        }
                        // var epsilonCell = getTableCell(firstTableID, prod.rule.right[i], epsilon);
                        if (epsilonCell.data != emptyCell) {
                            if (prod.rule.right.length - 1 != i) {
                                instructions.push(`Note that ${prod.rule.right[i]} is nullable, So we must also look at the next symbol in the production.`);
                            }
                        }
                        else {
                            break;
                        }
                    }
                }
                setInstructionValue(instructions.join("\n"));
                break;
            case Steps.FIND_FOLLOWS:
                var validRow = false;
                for (const symbol of prod.rule.right.values()) {
                    if (grammar.nonTerminals.has(symbol)) {
                        validRow = true;
                        break;
                    }
                }
                if (!validRow) {
                    break;
                }
                // Select the row
                this.selectProductionRow(row);
                // Disable all rules to start with
                for (const [key, value] of selectedProductionFollowCells.entries()) {
                    followTable.rulesData[key] = false;
                    selectedProductionFollowCells.set(key, new Set());
                }
                followTable.selectedRule = null;
                // Fill out the follow table selections that need to be made
                // for this production
                for (const [idx, symbol] of prod.rule.right.entries()) {
                    // Check if its a terminal
                    if (grammar.terminals.has(symbol)) {
                        // Nothing to do for a terminal
                        continue;
                    }
                    // Check if this is the last symbol
                    if (prod.rule.right.length <= idx + 1) {
                        // Last Symbol, Need to add Follow(LHS)
                        (_a = selectedProductionFollowCells.get(FollowRuleType.END_OF_PRODUCTION)) === null || _a === void 0 ? void 0 : _a.add({
                            rowLabel: symbol,
                            columnLabel: `Follow(${prod.rule.left})`
                        });
                        followTable.rulesData[FollowRuleType.END_OF_PRODUCTION] = true;
                        console.log(`Adding rule END_OF_PRODUCTION: Row ${symbol} , Column Follow(${prod.rule.left})`);
                        continue;
                    }
                    const followingSymbol = prod.rule.right[idx + 1];
                    // Check if the following symbol is terminal
                    if (grammar.terminals.has(followingSymbol)) {
                        // Terminal follows, Add the terminal
                        (_b = selectedProductionFollowCells.get(FollowRuleType.TERMINAL_FOLLOWS)) === null || _b === void 0 ? void 0 : _b.add({
                            rowLabel: symbol,
                            columnLabel: followingSymbol
                        });
                        followTable.rulesData[FollowRuleType.TERMINAL_FOLLOWS] = true;
                        console.log(`Adding rule TERMINAL_FOLLOWS: Row ${symbol} , Column ${followingSymbol}`);
                        continue;
                    }
                    ;
                    // Check for a non-terminal
                    if (grammar.nonTerminals.has(followingSymbol)) {
                        // Non-Terminal follows, Add its First set
                        (_c = selectedProductionFollowCells.get(FollowRuleType.NON_TERMINAL_FOLLOWS)) === null || _c === void 0 ? void 0 : _c.add({
                            rowLabel: symbol,
                            columnLabel: `First(${followingSymbol})`
                        });
                        followTable.rulesData[FollowRuleType.NON_TERMINAL_FOLLOWS] = true;
                        console.log(`Adding rule NON_TERMINAL_FOLLOWS: Row ${symbol} , Column First(${followingSymbol})`);
                        continue;
                    }
                }
                // Update the instructions
                setInstructionValue("Now select a rule in the Follow Rules table that applies to this production.");
                followTable.render();
                break;
            default:
                break;
        }
        this.render();
        return null;
    }
}
function resetError() {
    errorState = false;
    setInstructionValue("", true);
    setErrorValue("");
    var instructions = document.getElementById(messageTableID);
    instructions.style.color = HTMLColors.textColor;
    var messageBox = document.getElementById(messageParent);
    messageBox.style.backgroundColor = HTMLColors.softGreyColor;
}
// Error state caused by a left recursion
function grammarUnparsableError(errorStr) {
    setInstructionValue("", true);
    var instructions = document.getElementById(messageTableID);
    instructions.style.color = HTMLColors.defaultColor;
    var messageBox = document.getElementById(messageParent);
    messageBox.style.backgroundColor = HTMLColors.errorColor;
    setErrorValue(errorStr);
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
    constructor(grammar) {
        this.tableHeaderStr = "First Table";
        this.parentCellChildren = new Array();
        this.parentCellSelection = null;
        this.parentID = firstTableDiv;
        this.tableID = firstTableID;
        this.columns = new Array();
        this.rows = new Array();
        this.table = document.createElement("TABLE");
        grammar.nonTerminals.forEach((nonTerm) => {
            this.rows.push(nonTerm);
        });
        grammar.terminals.forEach((term) => {
            this.columns.push(term);
        });
        grammar.nonTerminals.forEach((value, key, map) => {
            this.columns.push(`First(${value})`);
        });
        this.columns.push(epsilon);
        this.tableData = new Map;
        this.rows.forEach((row) => {
            var newColumn = new Map();
            this.columns.forEach((column) => {
                newColumn.set(column, {
                    color: HTMLColors.defaultColor,
                    enabled: true,
                    data: emptyCell,
                    attributes: new Map()
                });
            });
            this.tableData.set(row, newColumn);
        });
        this.render();
    }
    setTableHeaderColor(color) {
        var header = this.table.caption;
        if (header != null) {
            header.style.backgroundColor = color;
        }
    }
    // Internal method for setting callback of cells
    _setTableCellCallback(cell, table, rowLabel, columnLabel) {
        cell.onclick = function () { table.cellCallback(rowLabel, columnLabel); };
        cell.style.cursor = "pointer";
    }
    // Render the table
    render() {
        var _a;
        // Remove old table
        deleteMyTable(this.tableID);
        // Create a new one based on the current state
        this.table = document.createElement("TABLE");
        this.table.setAttribute("id", this.tableID);
        this.table.style.border = "2px solid black";
        this.table.style.backgroundColor = HTMLColors.defaultColor;
        this.table.style.borderCollapse = "separate";
        // Add header
        var header = document.createElement("caption");
        header.textContent = this.tableHeaderStr;
        header.style.textAlign = "center";
        header.style.fontSize = "large";
        header.style.border = "2px solid black";
        header.style.backgroundColor = HTMLColors.softGreyColor;
        this.table.caption = header;
        // Build Rows
        for (var r = 0; r < this.rows.length + 1; r++) {
            var newRow = document.createElement("TR");
            this.table.appendChild(newRow);
            if (r == 0) {
                newRow.setAttribute("data-row", "HeaderRow");
            }
            else {
                newRow.setAttribute("data-row", this.rows[r - 1]);
            }
            for (var c = 0; c < this.columns.length + 1; c++) {
                var cell = document.createElement("TD");
                cell.style.color = "black";
                newRow.appendChild(cell);
                cell.style.minWidth = "50px";
                cell.style.border = "1px solid black";
                // Check if this is the header row
                if (r == 0) {
                    // Set header elements
                    if (c == 0) {
                        cell.setAttribute("data-column", "RowLabelColumn");
                        cell.textContent = "";
                        cell.style.backgroundColor = HTMLColors.softGreyColor;
                    }
                    else {
                        cell.setAttribute("data-column", this.columns[c - 1]);
                        // Set the Column Headers
                        cell.textContent = this.columns[c - 1];
                        cell.style.backgroundColor = HTMLColors.softGreyColor;
                    }
                }
                else {
                    if (c == 0) {
                        // Set Row labels
                        cell.setAttribute("data-column", "RowLabelColumn");
                        cell.textContent = this.rows[r - 1];
                        cell.style.backgroundColor = HTMLColors.softGreyColor;
                    }
                    else {
                        // Build first table cell locations
                        cell.setAttribute("data-column", this.columns[c - 1]);
                        var cellData = (_a = this.tableData.get(this.rows[r - 1])) === null || _a === void 0 ? void 0 : _a.get(this.columns[c - 1]);
                        if (cellData == null) {
                            cellData = {
                                color: HTMLColors.defaultColor,
                                enabled: true,
                                data: emptyCell,
                                attributes: new Map()
                            };
                        }
                        cell.style.backgroundColor = cellData.color;
                        cell.textContent = cellData.data;
                        // Add additional coloring for the epsilon column
                        if (this.columns[c - 1] === epsilon) {
                            if (cell.style.backgroundColor == HTMLColors.defaultColor) {
                                // Epsilon should be a slightly darker color
                                cell.style.backgroundColor = HTMLColors.epsilonColor;
                            }
                        }
                        // Add cell attributes
                        for (const [key, value] of cellData.attributes.entries()) {
                            cell.setAttribute(key, value);
                        }
                        if (cellData.enabled) {
                            // Add callback
                            this._setTableCellCallback(cell, this, this.rows[r - 1], this.columns[c - 1]);
                        }
                    }
                }
            }
        }
        var parent = document.getElementById(this.parentID);
        parent === null || parent === void 0 ? void 0 : parent.appendChild(this.table);
    }
    setCellEnable(rowLabel, columnLabel, enable) {
        var _a, _b;
        var cellData = (_a = this.tableData.get(rowLabel)) === null || _a === void 0 ? void 0 : _a.get(columnLabel);
        if (cellData == null) {
            cellData = {
                color: HTMLColors.defaultColor,
                enabled: true,
                data: emptyCell,
                attributes: new Map()
            };
        }
        cellData.enabled = enable;
        (_b = this.tableData.get(rowLabel)) === null || _b === void 0 ? void 0 : _b.set(columnLabel, cellData);
    }
    setCellColor(rowLabel, columnLabel, color) {
        var _a, _b;
        var cellData = (_a = this.tableData.get(rowLabel)) === null || _a === void 0 ? void 0 : _a.get(columnLabel);
        if (cellData == null) {
            cellData = {
                color: HTMLColors.defaultColor,
                enabled: true,
                data: emptyCell,
                attributes: new Map()
            };
        }
        cellData.color = color;
        (_b = this.tableData.get(rowLabel)) === null || _b === void 0 ? void 0 : _b.set(columnLabel, cellData);
    }
    disableAllCells() {
        var _a;
        for (const [rowKey, columns] of this.tableData.entries()) {
            for (const [columnKey, cell] of columns.entries()) {
                cell.enabled = false;
                (_a = this.tableData.get(rowKey)) === null || _a === void 0 ? void 0 : _a.set(columnKey, cell);
            }
        }
    }
    colorAllCells(color) {
        var _a;
        for (const [rowKey, columns] of this.tableData.entries()) {
            for (const [columnKey, cell] of columns.entries()) {
                cell.color = color;
                (_a = this.tableData.get(rowKey)) === null || _a === void 0 ? void 0 : _a.set(columnKey, cell);
            }
        }
    }
    setCellValue(rowLabel, columnLabel, data) {
        var _a, _b;
        var cellData = (_a = this.tableData.get(rowLabel)) === null || _a === void 0 ? void 0 : _a.get(columnLabel);
        if (cellData == null) {
            cellData = {
                color: HTMLColors.defaultColor,
                enabled: true,
                data: emptyCell,
                attributes: new Map()
            };
        }
        cellData.data = data;
        (_b = this.tableData.get(rowLabel)) === null || _b === void 0 ? void 0 : _b.set(columnLabel, cellData);
    }
    setCell(rowLabel, columnLabel, cellData) {
        var _a;
        (_a = this.tableData.get(rowLabel)) === null || _a === void 0 ? void 0 : _a.set(columnLabel, cellData);
    }
    getCell(rowLabel, columnLabel) {
        const row = this.tableData.get(rowLabel);
        if (row == null) {
            return null;
        }
        const cell = row.get(columnLabel);
        if (cell == null) {
            return null;
        }
        return cell;
    }
    // FirstTable cell Callback
    cellCallback(rowLabel, columnLabel) {
        var _a, _b, _c, _d, _e, _f, _g, _h, _j, _k;
        if (errorState == true) {
            return;
        }
        // var cell = getTableCell(this.tableID, rowLabel,columnLabel);
        var selectedCellData = this.getCell(rowLabel, columnLabel);
        switch (currentStep) {
            case Steps.ENTER_EPSILON:
                // Check that this cell matches the selected production rule.
                if (productionTable.selectedProduction == null) {
                    // No production selected just return
                    return;
                }
                // Check that the selected production rule's left side matches
                // the row label
                var selected_prod = productionTable.productions[productionTable.selectedProduction];
                if (selected_prod.rule.left == rowLabel) {
                    // Correct row, Check that this is the epsilon column
                    if (columnLabel == epsilon) {
                        // Correct choice, place the choice index in the cell
                        var cellData = (_a = this.tableData.get(rowLabel)) === null || _a === void 0 ? void 0 : _a.get(columnLabel);
                        if (cellData == null) {
                            cellData = {
                                color: HTMLColors.defaultColor,
                                enabled: true,
                                data: emptyCell,
                                attributes: new Map()
                            };
                        }
                        cellData.data = productionTable.selectedProduction.toString();
                        (_b = this.tableData.get(rowLabel)) === null || _b === void 0 ? void 0 : _b.set(columnLabel, cellData);
                        this.render();
                        checkProgress();
                    }
                    else {
                        // Not the epsilon column
                        setInstructionValue("The production rule should be placed in the epsilon column!");
                    }
                }
                else {
                    // Not the correct row
                    setInstructionValue(`The production rule should be placed in the ${selected_prod.rule.left} row!`);
                }
                break;
            case Steps.ENTER_EPSILON_FROM_EPSILON:
                // Check that this cell matches the selected production rule.
                if (productionTable.selectedProduction == null) {
                    // No production selected just return
                    return;
                }
                // Check that the selected production rule's left side matches
                // the row label
                var selected_prod = productionTable.productions[productionTable.selectedProduction];
                if (selected_prod.rule.left == rowLabel) {
                    // Correct row, Check that this is the epsilon column
                    if (columnLabel == epsilon) {
                        // Correct choice, place the choice index in the cell
                        var cellData = (_c = this.tableData.get(rowLabel)) === null || _c === void 0 ? void 0 : _c.get(columnLabel);
                        if (cellData == null) {
                            cellData = {
                                color: HTMLColors.defaultColor,
                                enabled: true,
                                data: emptyCell,
                                attributes: new Map()
                            };
                        }
                        if (cellData.data != emptyCell) {
                            // Check for left recursion
                            if (productionTable.selectedProduction.toString() != cellData.data) {
                                grammarUnparsableError(leftRecursionErrorStr);
                                break;
                            }
                        }
                        cellData.data = productionTable.selectedProduction.toString();
                        (_d = this.tableData.get(rowLabel)) === null || _d === void 0 ? void 0 : _d.set(columnLabel, cellData);
                        this.render();
                        checkProgress();
                    }
                    else {
                        // Not the epsilon column
                        setInstructionValue("The production rule should be placed in the epsilon column!");
                    }
                }
                else {
                    // Not the correct row
                    setInstructionValue(`The production rule should be placed in the ${selected_prod.rule.left} row!`);
                }
                break;
            case Steps.FIND_FIRSTS:
                // Check that this cell matches the selected production rule.
                if (productionTable.selectedProduction == null) {
                    // No production selected just return
                    return;
                }
                const prod = productionTable.productions[productionTable.selectedProduction];
                // Check that this is the correct row
                if (prod.rule.left != rowLabel) {
                    // Not the correct row
                    setErrorValue(`The production rule should be placed in the ${prod.rule.left} row!`);
                }
                else {
                    var stringComplete = false;
                    for (var i = 0; i < prod.rule.right.length; i++) {
                        var currentSymbol = prod.rule.right[i];
                        if (grammar.terminals.has(currentSymbol)) {
                            if (columnLabel == currentSymbol) {
                                // We should place the symbol
                                var cellData = (_e = this.tableData.get(rowLabel)) === null || _e === void 0 ? void 0 : _e.get(columnLabel);
                                if (cellData == null) {
                                    cellData = {
                                        color: HTMLColors.defaultColor,
                                        enabled: true,
                                        data: emptyCell,
                                        attributes: new Map()
                                    };
                                }
                                cellData.data = productionTable.selectedProduction.toString();
                                (_f = this.tableData.get(rowLabel)) === null || _f === void 0 ? void 0 : _f.set(columnLabel, cellData);
                                this.render();
                                checkProgress();
                                setErrorValue("");
                                stringComplete = true;
                                break;
                            }
                            else {
                                setErrorValue(`The production rule should be placed in the ${currentSymbol} column!`);
                                break;
                            }
                        }
                        else {
                            var correctColumn = `First(${currentSymbol})`;
                            if (correctColumn == columnLabel) {
                                if (selectedCellData == null) {
                                    return;
                                }
                                // Check if this cell is already set
                                if (selectedCellData.data != emptyCell && selectedCellData.data != productionTable.selectedProduction.toString()) {
                                    grammarUnparsableError(leftRecursionErrorStr);
                                    return;
                                }
                                // We should place the symbol
                                var cellData = (_g = this.tableData.get(rowLabel)) === null || _g === void 0 ? void 0 : _g.get(columnLabel);
                                if (cellData == null) {
                                    cellData = {
                                        color: HTMLColors.defaultColor,
                                        enabled: true,
                                        data: emptyCell,
                                        attributes: new Map()
                                    };
                                }
                                cellData.data = productionTable.selectedProduction.toString();
                                (_h = this.tableData.get(rowLabel)) === null || _h === void 0 ? void 0 : _h.set(columnLabel, cellData);
                                this.render();
                                checkProgress();
                                stringComplete = true;
                                setErrorValue("");
                                break;
                            }
                            else {
                                var epsilonCell = firstTable.getCell(currentSymbol, epsilon);
                                // Only continue if the symbol is nullable
                                // var epsilonCell = getTableCell(
                                //     firstTableID,
                                //     currentSymbol,
                                //     epsilon
                                // )
                                if ((epsilonCell === null || epsilonCell === void 0 ? void 0 : epsilonCell.data) != emptyCell) {
                                    continue;
                                }
                                else {
                                    setErrorValue(`Incorrect column! Try again`);
                                    stringComplete = true;
                                    break;
                                }
                            }
                        }
                    }
                    if (!stringComplete) {
                        setErrorValue(`Incorrect column! Try again`);
                        break;
                    }
                }
                break;
            case Steps.FIND_FIRSTS_COMPUTED:
                if (selectedCellData == null) {
                    return;
                }
                // Check if this a a value that needs to be simplified or one
                // that is a production of the backfill simplification
                if (selectedCellData.attributes.has(CellAttr.needsSimplified)) {
                    // This is a first cell that needs its values to be copied from
                    // the child cell row
                    // Deactivate all the other first table cells until this one is complete
                    this.colorAllCells(HTMLColors.disableColor);
                    this.disableAllCells();
                    selectedCellData.color = HTMLColors.errorColor;
                    selectedCellData.enabled = true;
                    // Get all the child cells
                    const copyRowKey = extractRowKey(columnLabel);
                    if (copyRowKey == null) {
                        // Something has gone horribly wrong
                        console.error(`First Table missing Row: "${copyRowKey}"`);
                        break;
                    }
                    // Don't copy the row if the row is itself
                    if (copyRowKey == rowLabel) {
                        // Mark the cell as complete
                        selectedCellData.data = emptyCell;
                        selectedCellData.color = HTMLColors.disableColor;
                        selectedCellData.attributes.delete(CellAttr.needsSimplified);
                        checkProgress();
                        break;
                    }
                    const copyRow = this.tableData.get(copyRowKey);
                    var rowNeedsUpdate = false;
                    for (const [childColumnKey, copyCell] of copyRow) {
                        if (copyCell.data == emptyCell) {
                            continue;
                        }
                        // Don't copy epsilon
                        if (childColumnKey == epsilon) {
                            continue;
                        }
                        // Don't copy first(itself)
                        if (childColumnKey == columnLabel) {
                            continue;
                        }
                        const childCell = this.getCell(rowLabel, childColumnKey);
                        // Check if this cell is already set to the same value and needs simplified
                        if (selectedCellData.data == childCell.data) {
                            // Already set to the same value, just continue
                            continue;
                        }
                        rowNeedsUpdate = true;
                        // This a column that needs to be copied.
                        copyCell.color = HTMLColors.darkHighlightColor;
                        this.parentCellChildren.push(childColumnKey);
                        // Enable and color the matching the cell in this row
                        childCell.color = HTMLColors.highlightColor;
                        childCell.enabled = true;
                        childCell.attributes.set(CellAttr.copyCellKey, copyRowKey);
                    }
                    this.parentCellSelection = { rowLabel, columnLabel };
                    setInstructionValue(`Place a ${selectedCellData.data} in all the columns in the ${rowLabel} row where there is a value in the ${copyRowKey} row.`);
                    if (!rowNeedsUpdate) {
                        // Mark the cell as complete
                        selectedCellData.data = emptyCell;
                        selectedCellData.color = HTMLColors.disableColor;
                        selectedCellData.attributes.delete(CellAttr.needsSimplified);
                        checkProgress();
                        setInstructionValue(`Select a new cell.`);
                    }
                }
                // Child Cell that needs to be filled
                else {
                    // Get parent cell
                    if (this.parentCellSelection == null) {
                        // Something has gone horribly wrong
                        console.error(`No parent row set for this cell!`);
                        break;
                    }
                    const parentCell = this.getCell((_j = this.parentCellSelection) === null || _j === void 0 ? void 0 : _j.rowLabel, (_k = this.parentCellSelection) === null || _k === void 0 ? void 0 : _k.columnLabel);
                    // Check for left recursion
                    if (selectedCellData.data != emptyCell) {
                        if (parentCell.data != selectedCellData.data) {
                            // Left Recursion
                            grammarUnparsableError(leftRecursionErrorStr);
                            break;
                        }
                    }
                    // Copy the parent cell data
                    selectedCellData.data = parentCell.data;
                    // Disable the child, Un-color it and the corresponding child cell
                    selectedCellData.color = HTMLColors.disableColor;
                    selectedCellData.enabled = false;
                    const copyCellRowKey = selectedCellData.attributes.get(CellAttr.copyCellKey);
                    firstTable.setCellColor(copyCellRowKey, columnLabel, HTMLColors.disableColor);
                    // Remove this cell from the remaining cells in the parent cell
                    const index = this.parentCellChildren.indexOf(columnLabel);
                    if (index > -1) {
                        this.parentCellChildren.splice(index, 1);
                    }
                    // Check if the parent cell is done
                    if (this.parentCellChildren.length == 0) {
                        // Mark the parent cell as complete
                        parentCell.data = emptyCell;
                        parentCell.color = HTMLColors.disableColor;
                        parentCell.attributes.delete(CellAttr.needsSimplified);
                        checkProgress();
                    }
                    // save all the changes
                    firstTable.setCell(rowLabel, this.parentCellSelection.columnLabel, parentCell);
                    firstTable.setCell(rowLabel, columnLabel, selectedCellData);
                }
                this.render();
                break;
            case Steps.FIND_FOLLOWS_COMPUTED_FIRSTS:
                // Verify that a follow table cell is selected
                if (followTable.selectedCell == null) {
                    break;
                }
                // Get the row to place the value in the follow table to
                const followRow = followTable.selectedCell.rowLabel;
                // Check if this is an epsilon column
                if (columnLabel == epsilon) {
                    // Nullable, need place to place in the follow column.
                    setInstructionValue(`Place an X in the Follow(${rowLabel}) column.`);
                    // Highlight and enable the cell in the follow table
                    var followCell = followTable.getCell(followRow, `Follow(${rowLabel})`);
                    if (followCell == null) {
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
                    if (followCell == null) {
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
                if (selectedCellData == null) {
                    break;
                }
                // Get the value from the selected follow table cell
                const followCellInfo = followTable.selectedCell;
                if (followCellInfo == null) {
                    break;
                }
                const selectedFollowCell = followTable.getCell(followCellInfo.rowLabel, followCellInfo.columnLabel);
                if (selectedFollowCell == null) {
                    break;
                }
                // Check if there is already different a value in this cell
                if (selectedCellData.data != emptyCell && selectedCellData.data != selectedFollowCell.data) {
                    grammarUnparsableError(unparsableGrammarErrorStr);
                }
                // Set the value disable both cells
                selectedCellData.data = selectedFollowCell.data;
                selectedCellData.color = HTMLColors.disableColor;
                selectedCellData.enabled = false;
                selectedFollowCell.color = HTMLColors.disableColor;
                selectedFollowCell.enabled = false;
                followTable.selectedCell = null;
                setInstructionValue("Good Now select another value in the follow table.");
                this.render();
                followTable.render();
                checkProgress();
                break;
            default:
                break;
        }
    }
}
class FollowTable {
    constructor(grammar) {
        this.renderRules = true;
        this.selectedCell = null;
        this.solvingFollowSet = new Set();
        this.parentID = followTableDiv;
        this.tableID = followTableID;
        this.hidden = false;
        this.columns = new Array();
        this.rows = new Array();
        this.table = document.createElement("TABLE");
        this.rulesTable = document.createElement("TABLE");
        this.selectedRule = null;
        this.rulesData = new Array(false, false, false);
        grammar.nonTerminals.forEach((nonTerm) => {
            this.rows.push(nonTerm);
        });
        grammar.terminals.forEach((term) => {
            this.columns.push(term);
        });
        grammar.nonTerminals.forEach((value, key, map) => {
            this.columns.push(`First(${value})`);
        });
        grammar.nonTerminals.forEach((value, key, map) => {
            this.columns.push(`Follow(${value})`);
        });
        this.tableData = new Map;
        this.rows.forEach((row) => {
            var newColumn = new Map();
            this.columns.forEach((column) => {
                newColumn.set(column, {
                    color: HTMLColors.defaultColor,
                    enabled: true,
                    data: emptyCell,
                    attributes: new Map()
                });
            });
            this.tableData.set(row, newColumn);
        });
        // By default set S,$, and add it to the follow set
        this.setCellValue("S", "$", "X");
        grammar.followSets.set("S", new Set("$"));
        this.render();
    }
    setTableHeaderColor(color) {
        var header = this.table.caption;
        if (header != null) {
            header.style.backgroundColor = color;
        }
    }
    setTableHidden(hidden) {
        this.hidden = hidden;
    }
    // Internal method for setting callback of cells
    _setTableCellCallback(cell, table, rowLabel, columnLabel) {
        cell.onclick = function () { table.cellCallback(rowLabel, columnLabel); };
        cell.style.cursor = "pointer";
    }
    // Internal method for setting callback of the rule table rows
    _setRuleTableCallback(row, table, ruleId) {
        row.onclick = function () { table.ruleRowCallback(ruleId); };
        row.style.cursor = "pointer";
    }
    // Render the table
    render() {
        var _a;
        // Remove old table
        deleteMyTable(this.tableID);
        deleteMyTable(followRulesID);
        if (this.hidden) {
            return;
        }
        // Create a new one based on the current state
        this.table = document.createElement("TABLE");
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
        for (var r = 0; r < this.rows.length + 1; r++) {
            var newRow = document.createElement("TR");
            this.table.appendChild(newRow);
            if (r == 0) {
                newRow.setAttribute("data-row", "HeaderRow");
            }
            else {
                newRow.setAttribute("data-row", this.rows[r - 1]);
            }
            for (var c = 0; c < this.columns.length + 1; c++) {
                var cell = document.createElement("TD");
                cell.style.color = "black";
                newRow.appendChild(cell);
                cell.style.minWidth = "50px";
                cell.style.paddingLeft = "8px";
                cell.style.paddingRight = "8px";
                cell.style.border = "1px solid black";
                // Check if this is the header row
                if (r == 0) {
                    // Set header elements
                    if (c == 0) {
                        cell.setAttribute("data-column", "RowLabelColumn");
                        cell.textContent = "";
                        cell.style.backgroundColor = HTMLColors.softGreyColor;
                    }
                    else {
                        cell.setAttribute("data-column", this.columns[c - 1]);
                        // Set the Column Headers
                        cell.textContent = this.columns[c - 1];
                        cell.style.backgroundColor = HTMLColors.softGreyColor;
                    }
                }
                else {
                    if (c == 0) {
                        // Set Row labels
                        cell.setAttribute("data-column", "RowLabelColumn");
                        cell.textContent = this.rows[r - 1];
                        cell.style.backgroundColor = HTMLColors.softGreyColor;
                    }
                    else {
                        // Build follow table cell locations
                        cell.setAttribute("data-column", this.columns[c - 1]);
                        var cellData = (_a = this.tableData.get(this.rows[r - 1])) === null || _a === void 0 ? void 0 : _a.get(this.columns[c - 1]);
                        if (cellData == null) {
                            cellData = {
                                color: HTMLColors.defaultColor,
                                enabled: true,
                                data: emptyCell,
                                attributes: new Map()
                            };
                        }
                        cell.style.backgroundColor = cellData.color;
                        cell.textContent = cellData.data;
                        // Add additional coloring for the epsilon column
                        if (this.columns[c - 1] === epsilon) {
                            if (cell.style.backgroundColor == HTMLColors.defaultColor) {
                                // Epsilon should be a slightly darker color
                                cell.style.backgroundColor = HTMLColors.epsilonColor;
                            }
                        }
                        // Add cell attributes
                        for (const [key, value] of cellData.attributes.entries()) {
                            cell.setAttribute(key, value);
                        }
                        if (cellData.enabled) {
                            // Add callback
                            this._setTableCellCallback(cell, this, this.rows[r - 1], this.columns[c - 1]);
                        }
                        // Override Style
                        if (cellData.attributes.has(CellAttr.styleOverride)) {
                            const overrides = cellData.attributes.get(CellAttr.styleOverride);
                            console.log("Cell Overrides: ", overrides);
                            if (overrides != null) {
                                const overridesMap = JSON.parse(overrides);
                                for (const [key, value] of Object.entries(overridesMap)) {
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
        parent === null || parent === void 0 ? void 0 : parent.appendChild(this.table);
        // Check if we should render the rules table
        if (this.renderRules) {
            // Build a Rules table
            this.rulesTable = document.createElement("TABLE");
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
            for (var r = 0; r < 3; r++) {
                var newRow = document.createElement("TR");
                var rule = FollowRules.get(r);
                if (rule == null) {
                    continue;
                }
                newRow.setAttribute("id", r.toString());
                newRow.style.border = "1px solid black";
                // Create index cell
                var idxCell = document.createElement("TD");
                idxCell.style.width = "24px";
                idxCell.style.border = "1px solid black";
                idxCell.style.color = "black";
                idxCell.style.backgroundColor = HTMLColors.softGreyColor;
                idxCell.textContent = r.toString();
                newRow.appendChild(idxCell);
                // Create Cell
                var cell = document.createElement("TD");
                newRow.appendChild(cell);
                cell.style.width = "350px";
                cell.style.border = "1px solid black";
                cell.style.color = "black";
                // Add rule
                cell.textContent = rule;
                // Set the row color
                if (this.selectedRule == r) {
                    newRow.style.backgroundColor = HTMLColors.highlightColor;
                    // Set the callback
                    this._setRuleTableCallback(newRow, this, r);
                }
                else if (this.rulesData[r]) {
                    newRow.style.backgroundColor = HTMLColors.defaultColor;
                    // Set the callback
                    this._setRuleTableCallback(newRow, this, r);
                }
                else {
                    newRow.style.backgroundColor = HTMLColors.disableColor;
                }
                this.rulesTable.appendChild(newRow);
            }
            parent === null || parent === void 0 ? void 0 : parent.appendChild(this.rulesTable);
        }
    }
    setCellAttr(rowLabel, columnLabel, attr, value) {
        var _a, _b;
        var cellData = (_a = this.tableData.get(rowLabel)) === null || _a === void 0 ? void 0 : _a.get(columnLabel);
        if (cellData == null) {
            cellData = {
                color: HTMLColors.defaultColor,
                enabled: true,
                data: emptyCell,
                attributes: new Map()
            };
        }
        cellData.attributes.set(attr, value);
        (_b = this.tableData.get(rowLabel)) === null || _b === void 0 ? void 0 : _b.set(columnLabel, cellData);
    }
    deleteCellAttr(rowLabel, columnLabel, attr) {
        var _a, _b;
        var cellData = (_a = this.tableData.get(rowLabel)) === null || _a === void 0 ? void 0 : _a.get(columnLabel);
        if (cellData == null) {
            cellData = {
                color: HTMLColors.defaultColor,
                enabled: true,
                data: emptyCell,
                attributes: new Map()
            };
        }
        cellData.attributes.delete(attr);
        (_b = this.tableData.get(rowLabel)) === null || _b === void 0 ? void 0 : _b.set(columnLabel, cellData);
    }
    setCellEnable(rowLabel, columnLabel, enable) {
        var _a, _b;
        var cellData = (_a = this.tableData.get(rowLabel)) === null || _a === void 0 ? void 0 : _a.get(columnLabel);
        if (cellData == null) {
            cellData = {
                color: HTMLColors.defaultColor,
                enabled: true,
                data: emptyCell,
                attributes: new Map()
            };
        }
        cellData.enabled = enable;
        (_b = this.tableData.get(rowLabel)) === null || _b === void 0 ? void 0 : _b.set(columnLabel, cellData);
    }
    setCellColor(rowLabel, columnLabel, color) {
        var _a, _b;
        var cellData = (_a = this.tableData.get(rowLabel)) === null || _a === void 0 ? void 0 : _a.get(columnLabel);
        if (cellData == null) {
            cellData = {
                color: HTMLColors.defaultColor,
                enabled: true,
                data: emptyCell,
                attributes: new Map()
            };
        }
        cellData.color = color;
        (_b = this.tableData.get(rowLabel)) === null || _b === void 0 ? void 0 : _b.set(columnLabel, cellData);
    }
    disableAllCells() {
        var _a;
        for (const [rowKey, columns] of this.tableData.entries()) {
            for (const [columnKey, cell] of columns.entries()) {
                cell.enabled = false;
                (_a = this.tableData.get(rowKey)) === null || _a === void 0 ? void 0 : _a.set(columnKey, cell);
            }
        }
    }
    colorAllCells(color) {
        var _a;
        for (const [rowKey, columns] of this.tableData.entries()) {
            for (const [columnKey, cell] of columns.entries()) {
                cell.color = color;
                (_a = this.tableData.get(rowKey)) === null || _a === void 0 ? void 0 : _a.set(columnKey, cell);
            }
        }
    }
    setCellValue(rowLabel, columnLabel, data) {
        var _a, _b;
        var cellData = (_a = this.tableData.get(rowLabel)) === null || _a === void 0 ? void 0 : _a.get(columnLabel);
        if (cellData == null) {
            cellData = {
                color: HTMLColors.defaultColor,
                enabled: true,
                data: emptyCell,
                attributes: new Map()
            };
        }
        cellData.data = data;
        (_b = this.tableData.get(rowLabel)) === null || _b === void 0 ? void 0 : _b.set(columnLabel, cellData);
    }
    setCell(rowLabel, columnLabel, cellData) {
        var _a;
        (_a = this.tableData.get(rowLabel)) === null || _a === void 0 ? void 0 : _a.set(columnLabel, cellData);
    }
    getCell(rowLabel, columnLabel) {
        const row = this.tableData.get(rowLabel);
        if (row == null) {
            return null;
        }
        const cell = row.get(columnLabel);
        if (cell == null) {
            return null;
        }
        return cell;
    }
    cellCallback(rowLabel, columnLabel) {
        if (errorState == true) {
            return;
        }
        var selectedCellData = this.getCell(rowLabel, columnLabel);
        if (selectedCellData == null) {
            return;
        }
        switch (currentStep) {
            case Steps.FIND_FOLLOWS:
                if (this.selectedRule == null) {
                    setErrorValue("You must select a Production and Rule first!");
                    return;
                }
                const selectedProductionCells = selectedProductionFollowCells.get(this.selectedRule);
                if (selectedProductionCells == null) {
                    break;
                }
                var correctSelection = false;
                for (var validCell of selectedProductionCells.values()) {
                    if (validCell.columnLabel == columnLabel && validCell.rowLabel == rowLabel) {
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
                if (productionTable.selectedProduction == null) {
                    break;
                }
                selectedCellData.data = 'X';
                // selectedCellData.data = productionTable.selectedProduction.toString()
                this.setCell(rowLabel, columnLabel, selectedCellData);
                // Add it to the follow set
                var followSet = grammar.followSets.get(rowLabel);
                if (followSet == null) {
                    followSet = new Set();
                }
                followSet.add(columnLabel);
                grammar.followSets.set(rowLabel, followSet);
                break;
            case Steps.FIND_FOLLOWS_COMPUTED_FIRSTS:
                // Check if this is a parent cell or child cell
                if (selectedCellData.attributes.has('data-ParentCell')) {
                    // Check if we are already solving a First() column
                    if (this.selectedCell != null) {
                        break;
                    }
                    // Select this cell
                    this.selectedCell = { rowLabel: rowLabel, columnLabel: columnLabel };
                    // Clear the current solving set
                    this.solvingFollowSet = new Set();
                    // Clear the highlighted cells in the first table
                    firstTable.colorAllCells(HTMLColors.disableColor);
                    firstTable.disableAllCells();
                    // Find which first table values need to be set in the follow table
                    const firstRowKey = extractRowKey(columnLabel);
                    if (firstRowKey == null) {
                        console.error("Column Symbol could not be found!");
                        return;
                    }
                    for (const firstColumnKey of firstTable.columns.values()) {
                        var firstCell = firstTable.getCell(firstRowKey, firstColumnKey);
                        if (firstCell == null) {
                            continue;
                        }
                        // Check if this cell is set
                        if (firstCell.data == emptyCell) {
                            continue;
                        }
                        var followChildColumnKey = "";
                        // Get the cell in the follow table that should be set by this cell
                        if (firstColumnKey == epsilon) {
                            // The first set can be epsilon, so we need the follow of this value
                            followChildColumnKey = `Follow(${firstRowKey})`;
                        }
                        else {
                            followChildColumnKey = firstColumnKey;
                        }
                        var followCell = followTable.getCell(rowLabel, followChildColumnKey);
                        if (followCell == null) {
                            continue;
                        }
                        // Check if its is already set
                        if (followCell.data != emptyCell) {
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
                    followTable.setCellValue(rowLabel, columnLabel, 'X');
                    followTable.setCellColor(rowLabel, columnLabel, HTMLColors.disableColor);
                    followTable.setCellEnable(rowLabel, columnLabel, false);
                    // Disable and color the corresponding first table cell
                    const firstParentRow = selectedCellData.attributes.get("data-FirstParentRow");
                    if (firstParentRow == null) {
                        break;
                    }
                    var firstParentCol = columnLabel;
                    if (!grammar.terminals.has(firstParentCol)) {
                        // Follow() column, first table parent cell is the epsilon column
                        firstParentCol = epsilon;
                    }
                    firstTable.setCellColor(firstParentRow, firstParentCol, HTMLColors.disableColor);
                    firstTable.setCellEnable(firstParentRow, firstParentCol, false);
                    // Remove it from the solving follow set and add it to grammar follow set
                    this.solvingFollowSet.delete(columnLabel);
                    var currentFollowSet = grammar.followSets.get(rowLabel);
                    if (currentFollowSet == null) {
                        currentFollowSet = new Set();
                    }
                    currentFollowSet.add(columnLabel);
                    // Check if we are done with the current selection
                    if (this.solvingFollowSet.size == 0) {
                        // Clear the selected cell
                        if (this.selectedCell == null) {
                            break;
                        }
                        var currentSelectedCell = followTable.getCell(this.selectedCell.rowLabel, this.selectedCell.columnLabel);
                        if (currentSelectedCell == null) {
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
                    if (this.selectedCell != null) {
                        // Clear out any already selected cell
                        for (const oldColumn of this.solvingFollowSet.values()) {
                            this.setCellEnable(this.selectedCell.rowLabel, oldColumn, false);
                            this.setCellColor(this.selectedCell.rowLabel, oldColumn, HTMLColors.disableColor);
                        }
                        this.solvingFollowSet.clear();
                    }
                    this.selectedCell = { rowLabel, columnLabel };
                    // Get the row that corresponds to this Follow() value
                    const followValueRowKey = extractRowKey(columnLabel);
                    if (followValueRowKey == null) {
                        console.error("Column Symbol could not be found!");
                        return;
                    }
                    // Check for a Row that follows itself
                    if (followValueRowKey == rowLabel) {
                        // Row that follows itself, Effectively already solved
                        setInstructionValue(`A Row that Follows itself is already solved.`);
                        // Clear the selected cell
                        this.selectedCell == null;
                        var currentSelectedCell = followTable.getCell(this.selectedCell.rowLabel, this.selectedCell.columnLabel);
                        if (currentSelectedCell == null) {
                            break;
                        }
                        currentSelectedCell.color = HTMLColors.disableColor;
                        currentSelectedCell.data = emptyCell;
                        currentSelectedCell.enabled = false;
                        currentSelectedCell.attributes.delete("data-ParentCell");
                        break;
                    }
                    const followValueRow = this.tableData.get(followValueRowKey);
                    if (followValueRow == null) {
                        break;
                    }
                    var allAlreadyFilled = true;
                    // Get the columns that are set in that row
                    for (const [followValueColumnKey, c] of followValueRow.entries()) {
                        if (c.data != emptyCell) {
                            // Check if that cell is already completed
                            var followSet = grammar.followSets.get(rowLabel);
                            if (followSet == null) {
                                continue;
                            }
                            if (followSet.has(followValueColumnKey)) {
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
                            setInstructionValue(`Fill in the values in the ${rowLabel} row where they are also set in the ${followValueRowKey} row`);
                        }
                    }
                    if (allAlreadyFilled == true) {
                        // All the values that processing this follow would fill
                        // already are so just continue.
                        setInstructionValue("Select a Follow table cell with a Follow() column to simplify.");
                        // Clear the selected cell
                        this.selectedCell == null;
                        var currentSelectedCell = followTable.getCell(this.selectedCell.rowLabel, this.selectedCell.columnLabel);
                        if (currentSelectedCell == null) {
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
                    followTable.setCellValue(rowLabel, columnLabel, 'X');
                    followTable.setCellColor(rowLabel, columnLabel, HTMLColors.disableColor);
                    followTable.setCellEnable(rowLabel, columnLabel, false);
                    // Remove it from the solving follow set and add it to grammar follow set
                    this.solvingFollowSet.delete(columnLabel);
                    var currentFollowSet = grammar.followSets.get(rowLabel);
                    if (currentFollowSet == null) {
                        currentFollowSet = new Set();
                    }
                    currentFollowSet.add(columnLabel);
                    // Check if we are done with the current selection
                    if (this.solvingFollowSet.size == 0) {
                        // Clear the selected cell
                        if (this.selectedCell == null) {
                            break;
                        }
                        var currentSelectedCell = followTable.getCell(this.selectedCell.rowLabel, this.selectedCell.columnLabel);
                        if (currentSelectedCell == null) {
                            break;
                        }
                        currentSelectedCell.color = HTMLColors.disableColor;
                        currentSelectedCell.data = emptyCell;
                        currentSelectedCell.enabled = false;
                        currentSelectedCell.attributes.delete("data-ParentCell");
                        // Remove the Follow() from the follow set
                        currentFollowSet.delete(`Follow(${rowLabel})`);
                        this.selectedCell = null;
                        setInstructionValue("Select a Follow table cell with a Follow() column to simplify.");
                    }
                }
                break;
            case Steps.PLACE_FOLLOW_EPSILON_NUMBERS:
                // Check if this is the nullable column
                if (columnLabel == nullableColumnKey) {
                    // Disable all cells
                    this.disableAllCells();
                    this.colorAllCells(HTMLColors.disableColor);
                    // Set this ones color back to red
                    this.setCellColor(rowLabel, columnLabel, HTMLColors.errorColor);
                    // Enable and highlight all cells in this row that aren't empty
                    for (const currentColumn of this.columns.values()) {
                        if (currentColumn == nullableColumnKey) {
                            continue;
                        }
                        const child = this.getCell(rowLabel, currentColumn);
                        if (child == null) {
                            continue;
                        }
                        if (child.data != emptyCell) {
                            // Highlight and enable
                            child.enabled = true;
                            child.color = HTMLColors.highlightColor;
                        }
                    }
                    setInstructionValue("Now copy the production rule's number to every cell set in this row.");
                }
                else {
                    // Child Cell, Update the value
                    const nullColumn = this.getCell(rowLabel, nullableColumnKey);
                    if (nullColumn == null) {
                        break;
                    }
                    selectedCellData.data = nullColumn.data;
                    selectedCellData.color = HTMLColors.disableColor;
                    selectedCellData.enabled = false;
                    const rowData = followTable.tableData.get(rowLabel);
                    if (rowData == null) {
                        break;
                    }
                    var rowComplete = true;
                    for (const [otherColumn, otherCell] of rowData.entries()) {
                        if (otherCell.data == "X") {
                            rowComplete = false;
                            break;
                        }
                    }
                    if (rowComplete) {
                        setInstructionValue("Good Now Select Another Nullable Row.");
                    }
                }
                break;
            case Steps.CREATE_FINAL_TABLE:
                if (this.selectedCell != null) {
                    // Disable the corresponding first table cell
                    firstTable.setCellColor(this.selectedCell.rowLabel, this.selectedCell.rowLabel, HTMLColors.disableColor);
                    firstTable.setCellEnable(this.selectedCell.rowLabel, this.selectedCell.rowLabel, false);
                }
                this.selectedCell = { rowLabel: rowLabel, columnLabel: columnLabel };
                // Select the corresponding first table cell
                const firstTableCell = firstTable.getCell(rowLabel, columnLabel);
                if (firstTableCell == null) {
                    console.error("Could not get first table cell!");
                    break;
                }
                // Enable it
                firstTableCell.color = HTMLColors.highlightColor;
                firstTableCell.enabled = true;
                // Render first table
                firstTable.render();
                setInstructionValue("Now place this cell in the matching cell in the First Table.");
                break;
            default:
                break;
        }
        this.render();
        checkProgress();
    }
    ruleRowCallback(rowId) {
        const selectedProductionCells = selectedProductionFollowCells.get(rowId);
        if (selectedProductionCells == null) {
            return;
        }
        if (selectedProductionCells.size == 0) {
            setErrorValue("The selected production does not use this rule! Try again.");
        }
        else {
            setInstructionValue("Now select a value in the follow table that corresponds with this rule.");
            this.selectedRule = rowId;
            followTable.render();
        }
    }
}
// Check the progress of the current step, advancing if necessary
function checkProgress(delayInstruction = true, userChoice = -1) {
    if (errorState == true) {
        return;
    }
    console.log(`Before progress Step: ${currentStep}`);
    switch (currentStep) {
        case Steps.ENTER_EPSILON:
            // Check that each production that produces epsilon has its first table
            // cell filled
            var done = true;
            for (var i = 0; i < productionTable.productions.length; i++) {
                var prod = productionTable.productions[i];
                // Check if the production should produce epsilon
                if (prod.rule.right[0] == epsilon) {
                    var cell = firstTable.getCell(prod.rule.left, epsilon);
                    // Check that its has been placed in the first table
                    if (cell != null) {
                        if ((cell === null || cell === void 0 ? void 0 : cell.data) != prod.idx.toString()) {
                            // Not complete yet
                            done = false;
                            break;
                        }
                    }
                }
            }
            // Check if done
            if (done == true) {
                // Move on to the next step
                currentStep = Steps.ENTER_EPSILON_FROM_EPSILON;
                if (productionTable.selectedProduction != null) {
                    productionTable.setProductionRowEnable(productionTable.selectedProduction, false);
                }
                setInstructionValue("Correct. Now choose a production rule that can produce epsilon indirectly.");
                checkProgress();
            }
            else {
                // Keep going
                if (productionTable.selectedProduction != null) {
                    productionTable.setProductionRowEnable(productionTable.selectedProduction, false);
                }
                if (first_pass == true) {
                    setInstructionValue("Select a production from the Production Table that can produce epsilon directly.");
                    first_pass = false;
                }
                else {
                    setInstructionValue("Correct, Now select another production that can produce epsilon directly.");
                }
            }
            break;
        case Steps.ENTER_EPSILON_FROM_EPSILON:
            var done = true;
            for (var i = 0; i < productionTable.productions.length; i++) {
                var prod = productionTable.productions[i];
                // Check if the production should produce epsilon indirectly
                var indirectlyEpsilon = true;
                for (var j = prod.rule.right.length - 1; j > -1; j--) {
                    var indirectEpsilonCol = firstTable.getCell(prod.rule.right[j], epsilon);
                    if (indirectEpsilonCol != null) {
                        // Check if the value is set
                        if (indirectEpsilonCol.data != emptyCell) {
                            continue;
                        }
                    }
                    indirectlyEpsilon = false;
                    break;
                }
                // Check if this was indirectly epsilon
                if (indirectlyEpsilon == true) {
                    // Check that this production indicates that it can also
                    // be epsilon
                    var current_cell = firstTable.getCell(prod.rule.left, epsilon);
                    if ((current_cell === null || current_cell === void 0 ? void 0 : current_cell.data) == emptyCell) {
                        // Not Done
                        done = false;
                        break;
                    }
                    else {
                        // Left recursion check
                        if ((current_cell === null || current_cell === void 0 ? void 0 : current_cell.data) != prod.idx.toString()) {
                            // Left recursion will happen
                            done = false;
                            break;
                        }
                    }
                }
            }
            // Check if done
            if (done == true) {
                // Move on to the next step
                currentStep = Steps.FIND_FIRSTS;
                if (productionTable.selectedProduction != null) {
                    productionTable.setProductionRowEnable(productionTable.selectedProduction, true);
                }
                setInstructionValue("Correct. Now choose a production rule and begin finding the First Values.");
                checkProgress();
            }
            else {
                if (productionTable.selectedProduction != null) {
                    productionTable.setProductionRowEnable(productionTable.selectedProduction, true);
                }
                setInstructionValue("Correct, Now select another production that can indirectly produce epsilon.");
            }
            break;
        case Steps.FIND_FIRSTS:
            var allProdsComplete = true;
            for (var j = 0; j < productionTable.productions.length; j++) {
                var prod = productionTable.productions[j];
                var prodComplete = true;
                // Walk through production and check if all of its firsts are placed
                for (var i = 0; i < prod.rule.right.length; i++) {
                    var currentSymbol = prod.rule.right[i];
                    if (grammar.terminals.has(currentSymbol) || currentSymbol == epsilon) {
                        var cell = firstTable.getCell(prod.rule.left, currentSymbol);
                        if ((cell === null || cell === void 0 ? void 0 : cell.data) != emptyCell) {
                            // Production complete
                            break;
                        }
                        else {
                            prodComplete = false;
                            break;
                        }
                    }
                    else {
                        var correctColumn = `First(${currentSymbol})`;
                        var cell = firstTable.getCell(prod.rule.left, correctColumn);
                        if ((cell === null || cell === void 0 ? void 0 : cell.data) == emptyCell) {
                            prodComplete = false;
                            break;
                        }
                        else {
                            // Only continue if the symbol is nullable,
                            var epsilonCell = firstTable.getCell(currentSymbol, epsilon);
                            if ((epsilonCell === null || epsilonCell === void 0 ? void 0 : epsilonCell.data) != emptyCell) {
                                // Check if the correct column is set with the same value
                                if ((cell === null || cell === void 0 ? void 0 : cell.data) != prod.idx.toString()) {
                                    // Not complete yet, Left recursion will happen
                                    prodComplete = false;
                                    break;
                                }
                                // Is nullable, Continue
                                continue;
                            }
                            else {
                                // Done
                                if ((cell === null || cell === void 0 ? void 0 : cell.data) != prod.idx.toString()) {
                                    // Not complete yet, Left recursion may happen
                                    prodComplete = false;
                                    break;
                                }
                                break;
                            }
                        }
                    }
                }
                if (prodComplete) {
                    // Only print this message if the current production being
                    // Checked is the selected production
                    if (j == productionTable.selectedProduction) {
                        productionTable.setProductionRowEnable(j, false);
                        setErrorValue("");
                        setInstructionValue("Good Job. Now select another production.");
                    }
                }
                else {
                    allProdsComplete = false;
                }
            }
            if (allProdsComplete) {
                console.log("Step: Find Firsts complete.");
                setInstructionValue("Good Job, Now Lets backfill the First() values in the table.");
                // Now update the step and run another pass of check progress
                currentStep = Steps.FIND_FIRSTS_COMPUTED;
                checkProgress();
            }
            break;
        case Steps.FIND_FIRSTS_COMPUTED:
            // Walk through all the first columns
            firstTable.disableAllCells();
            firstTable.colorAllCells(HTMLColors.disableColor);
            var stepDone = true;
            for (const columnKey of grammar.nonTerminals) {
                for (const rowKey of grammar.nonTerminals) {
                    const cell = firstTable.getCell(rowKey, `First(${columnKey})`);
                    if (cell == null) {
                        continue;
                    }
                    // Check if the cell is set
                    if (cell.data == emptyCell) {
                        continue;
                    }
                    // Cell is set, not done yet
                    stepDone = false;
                    // Set the cell color and enable
                    cell.color = HTMLColors.errorColor;
                    cell.enabled = true;
                    cell.attributes.set(CellAttr.needsSimplified, "true");
                }
            }
            if (stepDone) {
                // Move on to next step
                currentStep = Steps.FOLLOW_NEEDED;
                // prepForFollowSolve();
                setInstructionValue("Do we need to do the follow table? ");
                checkProgress();
            }
            break;
        case Steps.FOLLOW_NEEDED:
            // hidden
            noButton.style.visibility = "visible";
            yesButton.style.visibility = "visible";
            // Check if we need a follow table
            var needed = false;
            for (const symbol of grammar.nonTerminals) {
                const epsilonCol = firstTable.getCell(symbol, epsilon);
                if (epsilonCol == null) {
                    continue;
                }
                if (epsilonCol.data != emptyCell) {
                    needed = true;
                    break;
                }
            }
            if (userChoice != -1) {
                if (userChoice == 1 && needed) {
                    currentStep = Steps.FIND_FOLLOWS;
                    noButton.style.visibility = "hidden";
                    yesButton.style.visibility = "hidden";
                    prepForFollowSolve();
                    checkProgress();
                }
                else if (userChoice == 0 && needed) {
                    setErrorValue("We need a follow table as there are productions that can be epsilon!");
                }
                else if (userChoice == 1 && !needed) {
                    setErrorValue("We don't need a follow table as there are not productions that can be epsilon!");
                }
                else {
                    currentStep = Steps.DONE;
                    noButton.style.visibility = "hidden";
                    yesButton.style.visibility = "hidden";
                    checkProgress();
                }
            }
            break;
        case Steps.FIND_FOLLOWS:
            // Check if a rule and production are selected
            if (followTable.selectedRule == null || productionTable.selectedProduction == null) {
                // Rule hasn't been selected, move on
                break;
            }
            var selectedCells = selectedProductionFollowCells.get(followTable.selectedRule);
            if (selectedCells == null) {
                break;
            }
            // Check if the selected rule was the last of the current type
            if (selectedCells.size == 0) {
                // Unselect this rule
                followTable.selectedRule = null;
                setInstructionValue("Good, Now select another Rule from the Follow Rules table.");
            }
            var allRulesComplete = true;
            for (const [ruleId, ruleCells] of selectedProductionFollowCells) {
                if (ruleId > 2) {
                    continue;
                }
                if (ruleCells.size != 0) {
                    followTable.rulesData[ruleId] = true;
                    allRulesComplete = false;
                }
                else {
                    // Disable that rule
                    followTable.rulesData[ruleId] = false;
                }
            }
            // Check if all the rules have been finished for this production
            if (allRulesComplete) {
                // Disable selected Production and move on
                productionTable.setProductionRowEnable(productionTable.selectedProduction, false);
                setInstructionValue("Good, Now select another Production from the Production Table.");
            }
            // Check if all productions have been finished
            var done = true;
            for (const prod of productionTable.productions) {
                if (prod.enabled) {
                    done = false;
                    break;
                }
            }
            if (done) {
                // Done with this step
                setInstructionValue("Good Job. Now we need to simplify the First columns in the follow table. Select a Follow table cell with a First() column to simplify.");
                currentStep = Steps.FIND_FOLLOWS_COMPUTED_FIRSTS;
                // Hide the rules table
                followTable.renderRules = false;
                // Disable all cells to start
                followTable.disableAllCells();
                followTable.colorAllCells(HTMLColors.disableColor);
                // Highlight all the cells in the First() columns, and enable them
                for (const c of grammar.nonTerminals.values()) {
                    const columnKey = `First(${c})`;
                    for (const rowKey of grammar.nonTerminals.values()) {
                        var followCell = followTable.getCell(rowKey, columnKey);
                        if (followCell == null) {
                            continue;
                        }
                        else if (followCell.data != emptyCell) {
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
            if (followTable.selectedCell != null) {
                // Already solving a First()
                setInstructionValue("Select a highlighted cell in the First table to place in the Follow table.");
            }
            // Check if all the First() values are solved
            else if (followTable.solvingFollowSet.size == 0) {
                // Just solved the First() column
                followTable.selectedCell = null;
                setInstructionValue("Select a Follow table cell with a First() column to simplify.");
            }
            var done = true;
            // Check if we have solved all the First Columns
            for (const c of grammar.nonTerminals.values()) {
                const columnKey = `First(${c})`;
                for (const rowKey of grammar.nonTerminals.values()) {
                    var followCell = followTable.getCell(rowKey, columnKey);
                    if (followCell == null) {
                        continue;
                    }
                    else if (followCell.data != emptyCell) {
                        // Still Solving
                        done = false;
                    }
                }
            }
            if (done) {
                // Move to next step
                currentStep = Steps.FIND_FOLLOWS_COMPUTED_FOLLOWS;
                // Hide the First() columns
                for (const nonTerm of grammar.nonTerminals) {
                    const column = `First(${nonTerm})`;
                    const idx = followTable.columns.indexOf(column);
                    if (idx < 0) {
                        continue;
                    }
                    followTable.columns.splice(idx, 1);
                    for (const followColumn of followTable.tableData.values()) {
                        followColumn.delete(column);
                    }
                }
                // Disable all cells to start
                followTable.disableAllCells();
                followTable.colorAllCells(HTMLColors.disableColor);
                // Highlight all the cells in the Follow() columns, and enable them
                for (const c of grammar.nonTerminals.values()) {
                    const columnKey = `Follow(${c})`;
                    for (const rowKey of grammar.nonTerminals.values()) {
                        var followCell = followTable.getCell(rowKey, columnKey);
                        if (followCell == null) {
                            continue;
                        }
                        else if (followCell.data != emptyCell) {
                            // Enable and highlight the cell
                            followCell.color = HTMLColors.errorColor;
                            followCell.enabled = true;
                            followCell.attributes.set("data-ParentCell", "true");
                            followTable.setCell(rowKey, columnKey, followCell);
                        }
                    }
                }
                setInstructionValue("Select a Follow table cell with a Follow() column to simplify.");
                checkProgress();
            }
            break;
        case Steps.FIND_FOLLOWS_COMPUTED_FOLLOWS:
            // Check if we are already solving a Follow Column
            if (followTable.selectedCell != null) {
            }
            // Check if all the Follow() values are solved
            else if (followTable.solvingFollowSet.size == 0) {
                // Just solved the Follow() column
                followTable.disableAllCells();
                followTable.colorAllCells(HTMLColors.disableColor);
                // Highlight all the cells in the Follow() columns, and enable them
                for (const c of grammar.nonTerminals.values()) {
                    const columnKey = `Follow(${c})`;
                    for (const rowKey of grammar.nonTerminals.values()) {
                        var followCell = followTable.getCell(rowKey, columnKey);
                        if (followCell == null) {
                            continue;
                        }
                        else if (followCell.data != emptyCell) {
                            // Enable and highlight the cell
                            followCell.color = HTMLColors.errorColor;
                            followCell.enabled = true;
                            followCell.attributes.set("data-ParentCell", "true");
                            followTable.setCell(rowKey, columnKey, followCell);
                        }
                    }
                }
                setInstructionValue("Select a Follow table cell with a Follow() column to simplify.");
                followTable.selectedCell = null;
            }
            var done = true;
            // Check if we have solved all the Follow Columns
            for (const c of grammar.nonTerminals.values()) {
                const columnKey = `Follow(${c})`;
                for (const rowKey of grammar.nonTerminals.values()) {
                    var followCell = followTable.getCell(rowKey, columnKey);
                    if (followCell == null) {
                        continue;
                    }
                    else if (followCell.data != emptyCell) {
                        // Still Solving
                        done = false;
                    }
                }
            }
            if (done) {
                // We have build the tables
                // Hide the Follow() columns
                for (const nonTerm of grammar.nonTerminals) {
                    const column = `Follow(${nonTerm})`;
                    const idx = followTable.columns.indexOf(column);
                    if (idx < 0) {
                        continue;
                    }
                    followTable.columns.splice(idx, 1);
                    for (const followColumn of followTable.tableData.values()) {
                        followColumn.delete(column);
                    }
                }
                // Disable all cell
                followTable.disableAllCells();
                firstTable.disableAllCells();
                // Color them normally
                followTable.colorAllCells(HTMLColors.defaultColor);
                firstTable.colorAllCells(HTMLColors.defaultColor);
                // Mark as done
                currentStep = Steps.PLACE_FOLLOW_EPSILON_NUMBERS;
                setInstructionValue([
                    "Good Job, The First and Follow tables are now complete! ",
                    "Now We will place the production rules # that are nullable ",
                    "in the follow table to see what follow table values we will need.",
                    " The Epsilon Column from the first table is what determines if a ",
                    "Production is nullable. It has been copied to the follow table for now. ",
                    "Select A highlighted Nullable cell to begin."
                ].join(''));
                prepForFollowIdxPlacement();
            }
            break;
        case Steps.PLACE_FOLLOW_EPSILON_NUMBERS:
            // Verify that all Nullable rows have their indexes placed
            var done = true;
            for (const rowKey of followTable.rows.values()) {
                // Check if this row is nullable
                const nullColumn = followTable.getCell(rowKey, nullableColumnKey);
                if (nullColumn == null) {
                    continue;
                }
                if (nullColumn.data == emptyCell) {
                    continue;
                }
                var rowComplete = true;
                // Check all the columns for the correct index
                for (const columnKey of followTable.columns.values()) {
                    if (columnKey == nullableColumnKey) {
                        continue;
                    }
                    const cellData = followTable.getCell(rowKey, columnKey);
                    if (cellData == null) {
                        continue;
                    }
                    if (cellData.data == emptyCell) {
                        continue;
                    }
                    if (cellData.data != nullColumn.data) {
                        // Not Done
                        done = false;
                        rowComplete = false;
                    }
                }
                if (rowComplete) {
                    // Disable the null column
                    nullColumn.color = HTMLColors.disableColor;
                    nullColumn.enabled = false;
                }
                else {
                    nullColumn.color = HTMLColors.errorColor;
                    nullColumn.enabled = true;
                }
            }
            if (done == true) {
                // Update for next state
                currentStep = Steps.CREATE_FINAL_TABLE;
                // Remove null column
                let index = followTable.columns.indexOf(nullableColumnKey);
                if (index > -1) {
                    followTable.columns.splice(index, 1);
                }
                setInstructionValue([
                    "Now we can build the Final Production Table. ",
                    "We will use the first table as our final production table. ",
                    "To create the Final Production Table, we need to fill the ",
                    "First table with the Follow Table Values. ",
                    "Select a Follow Table Value to begin. "
                ].join(''));
                currentStep = Steps.CREATE_FINAL_TABLE;
                prepForFinalTableBuild();
            }
            break;
        case Steps.CREATE_FINAL_TABLE:
            // Check if all the follow table cells have been placed
            var done = true;
            for (const [rowKey, columnMap] of followTable.tableData) {
                if (followTable.rows.indexOf(rowKey) == -1) {
                    continue;
                }
                for (const columnKey of followTable.columns.values()) {
                    if (followTable.columns.indexOf(columnKey) == -1) {
                        continue;
                    }
                    const cellData = columnMap.get(columnKey);
                    if (cellData == null) {
                        continue;
                    }
                    if (cellData.enabled == true) {
                        done = false;
                        break;
                    }
                }
            }
            if (done) {
                currentStep = Steps.DONE;
                // Hide the follow table
                followTable.hidden = true;
                // Update the first table name
                firstTable.tableHeaderStr = "Transition Table";
                // Remove epsilon column from first table
                let index = firstTable.columns.indexOf(epsilon);
                if (index > -1) {
                    firstTable.columns.splice(index, 1);
                }
                checkProgress();
            }
            break;
        case Steps.DONE:
            firstTable.colorAllCells(HTMLColors.defaultColor);
            setInstructionValue("The Transition Table is now complete.");
            var remainingFirstColumns = new Array();
            // Fill the table with the actual production rules
            for (const [rowKey, columnMap] of firstTable.tableData) {
                for (const columnKey of firstTable.columns.values()) {
                    if (columnKey.startsWith("First")) {
                        remainingFirstColumns.push(columnKey);
                    }
                    const cellData = columnMap.get(columnKey);
                    if (cellData == null) {
                        continue;
                    }
                    if (cellData.data != emptyCell) {
                        const prod = productionTable.productions[parseInt(cellData.data)];
                        cellData.data = `${prod.rule.left} ${assignmentSymbol} ${prod.rule.right.join("")}`;
                    }
                }
            }
            for (const firstCol of remainingFirstColumns) {
                const i = firstTable.columns.indexOf(firstCol);
                if (i > -1) {
                    firstTable.columns.splice(i, 1);
                }
            }
        default:
            break;
    }
    console.log(`After progress Step: ${currentStep}`);
    productionTable.render();
    firstTable.render();
    followTable.render();
}
// This function parses an array of strings, where each string is a production rule,
// into a structured Grammar object.
function createGrammar(input) {
    var _a;
    input_error_str = "";
    try {
        // Initialize an empty array for production rules.
        const rules = [];
        // Initialize sets for terminals and non-terminals.
        const terminals = new Set();
        const nonTerminals = new Set();
        const inputNonTerms = new Set();
        var followSets = new Map();
        // Collect epsilon and assignment symbol
        const assignmentElem = document.getElementById(assignmentSymId);
        if (assignmentElem.value == null) {
            return null;
        }
        assignmentSymbol = assignmentElem.value.trim();
        const epsilonElem = document.getElementById(epsilonSymId);
        if (epsilonElem.value == null) {
            return null;
        }
        epsilon = (_a = epsilonElem.value) === null || _a === void 0 ? void 0 : _a.trim();
        console.log("assignment: ", assignmentSymbol);
        console.log("epsilon: ", epsilon);
        if (["", "$", "S"].includes(assignmentSymbol) || ["", "$", "S"].includes(epsilon) || assignmentSymbol == epsilon) {
            console.error("Invalid Assignment or Epsilon Symbol!");
            input_error_str = "Invalid Assignment or Epsilon Symbol!";
            return null;
        }
        // Split input string into lines
        var inputLines = input.trim().split(/(?:\r?\n)+/);
        // Add the starting rule
        const [start, _] = inputLines[0].split(assignmentSymbol).map((s) => s.trim());
        nonTerminals.add("S");
        // Process each line of the grammar input.
        for (const line of inputLines) {
            const sides = line.split(assignmentSymbol).map((s) => s.trim());
            if (sides.length != 2) {
                console.error("Production cannot use the Assignment Symbol twice!");
                input_error_str = "Production cannot use the Assignment Symbol twice!";
                return null;
            }
            // The left-hand side is always a non-terminal.
            inputNonTerms.add(sides[0]);
            nonTerminals.add(sides[0]);
        }
        if (inputNonTerms.has("S")) {
            console.error("Invalid Production with non-term 'S'!");
            return null;
        }
        const productionStrings = [`S ${assignmentSymbol} ${start} $`].concat(inputLines);
        for (const line of productionStrings) {
            // Split the production rule by assignment symbol and remove extra whitespace.
            const [left, right] = line.split(assignmentSymbol, 2).map((s) => s.trim());
            // Split the right-hand side by the OR symbol ('|') to get alternative productions.
            // Each alternative represents a separate production rule.
            const alternatives = right.split("|").map(alt => alt.trim());
            // Process each alternative.
            for (const alt of alternatives) {
                // Split the alternative into individual symbols by spaces.
                // Filter out any empty strings that might occur due to extra whitespace.
                const rightSymbols = alt.split(" ").filter(sym => sym.length > 0);
                // If the production only contains epsilon, keep it as is
                if (rightSymbols.length === 1 && rightSymbols[0] === epsilon) {
                    // Check that this production is not already in the rules
                    if (rules.some(rule => rule.left === left && rule.right.every((element, index) => element === rightSymbols[index]))) {
                        // Rule already exists
                        continue;
                    }
                    rules.push({ left, right: rightSymbols });
                    continue;
                }
                // Remove epsilon from the production if it contains other symbols
                const filteredProduction = rightSymbols.filter(symbol => symbol !== epsilon);
                // If after removing epsilon the production is not empty, add it
                if (filteredProduction.length > 0) {
                    if (rules.some(rule => rule.left === left && rule.right.every((element, index) => element === rightSymbols[index]))) {
                        // Rule already exists
                        continue;
                    }
                    rules.push({ left, right: filteredProduction });
                }
                var badRightSymbol = false;
                // Determine if each symbol on the right-hand side is a terminal or non-terminal.
                filteredProduction.forEach((symbol) => {
                    console.log(`Right Symbol: ${symbol}`);
                    // Skip for epsilon
                    if (symbol == epsilon) {
                    }
                    // Check if the symbol is the assignment symbol
                    else if (symbol == assignmentSymbol) {
                        console.error("Production cannot use the Assignment Symbol twice!");
                        input_error_str = "Production cannot use the Assignment Symbol twice!";
                        badRightSymbol = true;
                    }
                    // Check if they are using the Start symbol
                    else if (symbol == "S") {
                        console.error("Invalid Production with non-term 'S'!");
                        input_error_str = "Cannot use reserved Start Symbol S!";
                        badRightSymbol = true;
                    }
                    else if (!(nonTerminals.has(symbol))) {
                        terminals.add(symbol);
                    }
                });
                if (badRightSymbol) {
                    return null;
                }
            }
        }
        // Populate the first and follow sets
        nonTerminals.forEach((term) => {
            followSets.set(term, new Set());
        });
        // Check for empty productions
        if (nonTerminals.size == 0) {
            // No productions entered
            return null;
        }
        if (terminals.has(epsilon) || terminals.has(assignmentSymbol)) {
            // Epsilon or Assignment symbol is a terminal
            console.error("Epsilon or Assignment Symbol is a Terminal!");
            input_error_str = "Epsilon or Assignment Symbol is a Terminal!";
            return null;
        }
        if (nonTerminals.has(epsilon) || nonTerminals.has(assignmentSymbol)) {
            // Epsilon or Assignment symbol is a non-terminal
            console.error("Epsilon or Assignment Symbol is a Non-Terminal!");
            input_error_str = "Epsilon or Assignment Symbol is a Non-Terminal!";
            return null;
        }
        // Always one terminal of $
        if (terminals.size == 1) {
            console.error("No Non-Terminals Found!");
            input_error_str = "No Non-Terminals Found in grammar!";
            return null;
        }
        // Return the structured grammar object with empty FIRST and FOLLOW sets.
        return {
            terminals,
            nonTerminals,
            rules,
            followSets,
        };
    }
    catch (error) {
        console.error("Could not parse input Grammar!");
        return null;
    }
}
// Prepares for the follow table to be solved
function prepForFollowSolve() {
    // Un-hide the table
    followTable.setTableHidden(false);
    followTable.renderRules = true;
    // Enable all the rows in the production table that contain non-terminals,
    // Disabling others
    for (var i = 0; i < productionTable.productions.length; i++) {
        const prod = productionTable.productions[i];
        var enableRow = false;
        for (const symbol of prod.rule.right.values()) {
            if (grammar.nonTerminals.has(symbol)) {
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
    for (const nonTerm of grammar.nonTerminals) {
        const column = `First(${nonTerm})`;
        const idx = firstTable.columns.indexOf(column);
        if (idx < 0) {
            continue;
        }
        firstTable.columns.splice(idx, 1);
        for (const firstColumn of firstTable.tableData.values()) {
            firstColumn.delete(column);
        }
    }
    // Render tables
    firstTable.render();
    followTable.render();
    productionTable.render();
    setInstructionValue("Now we can begin to solve the Follow Table. Select a production that contains a non-terminal in its right hand side to begin.");
}
// Prepare the follow table for solving the nullable sets after it has been
// completed
function prepForFollowIdxPlacement() {
    followTable.columns.push(nullableColumnKey);
    // Render to create new column
    followTable.render();
    followTable.disableAllCells();
    followTable.colorAllCells(HTMLColors.disableColor);
    // Fill the data from the first table
    for (const [rowKey, columnMap] of firstTable.tableData) {
        const cellData = columnMap.get(epsilon);
        var data = cellData === null || cellData === void 0 ? void 0 : cellData.data;
        followTable.setCellValue(rowKey, nullableColumnKey, data);
        // Add style override
        const cellStyle = {
            "border-left": "3px solid black",
            "border-right": "3px solid black",
            "border-collapse": "collapse"
        };
        followTable.setCellAttr(rowKey, nullableColumnKey, CellAttr.styleOverride, JSON.stringify(cellStyle));
        if (data != emptyCell) {
            // Row will need to be filled
            followTable.setCellColor(rowKey, nullableColumnKey, HTMLColors.errorColor);
            followTable.setCellEnable(rowKey, nullableColumnKey, true);
        }
        else {
            followTable.setCellColor(rowKey, nullableColumnKey, HTMLColors.disableColor);
            followTable.setCellEnable(rowKey, nullableColumnKey, false);
        }
        console.log(rowKey, columnMap.get(epsilon));
    }
    followTable.render();
}
// Prepare to place the final values in the first table
function prepForFinalTableBuild() {
    // Render follow to flush values
    followTable.render();
    // Disable all cells in both tables
    firstTable.disableAllCells();
    firstTable.colorAllCells(HTMLColors.disableColor);
    followTable.disableAllCells();
    followTable.colorAllCells(HTMLColors.disableColor);
    // Enable any cells in the follow table that have a value set
    var removeRows = [];
    var rowNeeded = false;
    for (const [rowKey, columnMap] of followTable.tableData) {
        rowNeeded = false;
        for (const columnKey of followTable.columns.values()) {
            const cellData = columnMap.get(columnKey);
            if (cellData == null) {
                continue;
            }
            if (cellData.data == "X") {
                continue;
            }
            else if (cellData.data != emptyCell) {
                rowNeeded = true;
                cellData.color = HTMLColors.errorColor;
                cellData.enabled = true;
            }
        }
        if (rowNeeded == false) {
            removeRows.push(rowKey);
        }
    }
    // Remove un-needed rows
    followTable.rows = followTable.rows.filter(item => !removeRows.includes(item));
    followTable.render();
    firstTable.render();
    checkProgress();
}
// Start the Parser and build the starting tables, OnClick function for the
// grammar input box "=>" button
function startParser() {
    // Collect and use the input from the user
    resetError();
    let inputBox = document.getElementById(grammarInputBox);
    if (inputBox == null) {
        // Could not acquire the input box element
        return null;
    }
    grammar = createGrammar(inputBox.value);
    if (grammar == null) {
        setInstructionValue("");
        if (input_error_str == "") {
            setErrorValue("Could Not Parse the inputted grammar. Please check for typos and try again!");
        }
        else {
            setErrorValue(input_error_str);
            input_error_str = "";
        }
    }
    else {
        currentStep = Steps.ENTER_EPSILON;
        productionTable = new ProductionTable(grammarProductionColumn, grammar);
        firstTable = new FirstTable(grammar);
        followTable = new FollowTable(grammar);
        // Hide the follow table for now
        followTable.setTableHidden(true);
        followTable.render();
        setInstructionValue("Select a production that can produce epsilon directly.");
        setErrorValue("");
        first_pass = true;
        checkProgress();
    }
}
// Set up for the page
function setup() {
    let inputBox = document.getElementById(grammarInputBox);
    if (inputBox != null) {
        console.log(defaultGrammar);
        inputBox.innerHTML = defaultGrammar;
    }
    currentStep = Steps.ENTER_GRAMMAR;
    setInstructionValue("Enter a grammar and hit the => to start, Or select Random.");
}
function generateRandomCharacter(alphabet) {
    const randomIndex = Math.floor(Math.random() * alphabet.length * alphabet.length) % alphabet.length;
    return alphabet[randomIndex];
}
function getRandomProduction(L, nonTerminals = sampleNonTerminals, maxLen = 10) {
    const length = Math.floor(Math.random() * 100) % maxLen + 1;
    var availNonTerms = nonTerminals.split(L).join("");
    var RHS = new Array;
    if (Math.random() > 0.4) {
        // Just other non terms
        for (var i = 0; i < length; i++) {
            // Non-Terminal
            const randChar = generateRandomCharacter(availNonTerms);
            availNonTerms = availNonTerms.split(randChar).join("");
            RHS.push(randChar);
        }
    }
    else {
        for (var i = 0; i < length; i++) {
            if (Math.random() > 0.9) {
                // Non-Terminal
                const randChar = generateRandomCharacter(availNonTerms);
                availNonTerms = availNonTerms.split(randChar).join("");
                RHS.push(randChar);
            }
            else {
                // Terminal
                RHS.push(generateRandomCharacter(sampleTerminals));
            }
        }
    }
    return `${L} ${assignmentSymbol} ${RHS.join(" ")}`;
}
// Random Grammar Button
function randomGrammar() {
    console.log("Creating Random Productions...");
    var numberOfNonTerminals = Math.floor((Math.random() * 10)) % 5;
    if (numberOfNonTerminals < 3) {
        numberOfNonTerminals = numberOfNonTerminals + 3;
    }
    var possibleNonTerms = sampleNonTerminals;
    var nonTerminals = "";
    for (var i = 0; i < numberOfNonTerminals; i++) {
        const randChar = generateRandomCharacter(possibleNonTerms);
        nonTerminals = nonTerminals + randChar;
        possibleNonTerms = possibleNonTerms.split(randChar).join("");
    }
    console.log(`# ${numberOfNonTerminals} NonTerms: ${nonTerminals}`);
    var productions = new Array();
    var chance = Math.random();
    for (var i = 0; i < nonTerminals.length; i++) {
        var LHS = nonTerminals[i];
        var repeat = true;
        if ((nonTerminals.length - 3) - i < 0) {
            productions.push(`${LHS} ${assignmentSymbol} ${epsilon}`);
        }
        while (repeat) {
            var prod = getRandomProduction(LHS, nonTerminals);
            console.log(prod);
            productions.push(prod);
            if (Math.random() < chance) {
                chance = chance / 2;
                console.log(`Creating additional production for nonTerm: ${LHS}`);
                continue;
            }
            else {
                repeat = false;
            }
        }
    }
    var joinedProductions = productions.join("\n");
    console.log("Productions: ");
    console.log(joinedProductions);
    let inputBox = document.getElementById(grammarInputBox);
    console.log(inputBox);
    if (inputBox != null) {
        inputBox.value = joinedProductions;
    }
}
const sampleTerminals = '+-()';
const sampleNonTerminals = 'ABCDEFGHIJKLMNOPQRTUVWXYZ';
function handleYes() {
    checkProgress(false, 1);
}
function handleNo() {
    checkProgress(false, 0);
}
//# sourceMappingURL=parser.js.map