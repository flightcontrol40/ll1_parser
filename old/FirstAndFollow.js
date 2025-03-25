
const Steps = Object.freeze({ 
    INVALID: -1, 
    ENTER_Grammar: 0,
    ENTER_EPSILON: 1, // Still to do: If rule is entirely nonterminals and all can be e it is also e
    ENTER_EPSILON_FROM_EPSILON: 2, 
    FIND_FIRSTS: 3, 
    FIND_FIRSTS_COMPUTED: 4, 
    FIND_FOLLOWS: 5, 
    FIND_FOLLOWS_COMPUTED_FIRSTS: 6, 
    FIND_FOLLOWS_COMPUTED_FOLLOWS: 7, 
    
    DONE: 9 
}); 

const StepsDescriptive = [
    "Enter your grammar in the box below or press the random button.",
    "Find all directly NULLABLE non-terminals",
    "Find all indirectly NULLABLE non-terminals",
    "Fill in the Firsts table from the Grammar",
    "Simplify the Firsts in the First Table",
    "Fill in the Follows from the Grammar",
    "Simplify the Follows in the Follow Table",
    "Add the follow information on any row that is NULLABLE", 
];

const FirstSteps = Object.freeze({ 
    INVALID: -1, 
    SELF_RECURSIVE: 1, // Still to do: If rule is entirely nonterminals and all can be e it is also e
    SIMPLE: 2, 
    MULTI_RECURSIVE: 3, 

    DONE: 9 
});

var step = Steps.INVALID;
var firststep = FirstSteps.INVALID;
var numNodes = 1;
var grammar;
var messageTableId = "messageTable";
var grammerTable = "myTable";
var firstTable = "firstTable";
var followTable = "followTable";
var mTable = "mTable";
var currentX = 0;
var currentRule = -1;
var toRow = -1;
var fromRow = -1;
var updateValue = -1;

var nonTerminals = [];
var terminals = [];
var grammarRuleComplete = [];
var nonTerminalFirstRowComplete = [];
var nonTerminalFollowRowComplete = [];
var epsilonCol;
var grammarLength;
var nonTerminalsLength;
var terminalsLength;


const emptyCell = ".";
const epsilon = "e";

const defaultColor = "white";
const highlightColor = "yellow";
const disableColor = "gray";
const accentColor = "red";
const buttonColor = "#dddddd";
const nulledNonTerminalColor = "#eeeeee";
            
////////////Helper Variables
var helperFirstEpsilon = 0;            

////////////Helper Functions/////////////////////////////    
function resetHelpMe() {
        let randomButton  = document.getElementById("RandomButton"); 
        randomButton.style.background = buttonColor;
        
        randomButton  = document.getElementById("userGrammarButton"); 
        randomButton.style.background = buttonColor;
}

function helpMe() {
    //alert("Help");
    if(step == Steps.ENTER_Grammar) {
        let randomButton  = document.getElementById("RandomButton"); 
        randomButton.style.background = highlightColor;
        instruction("Click 'Random' to get a pre-made grammar.");                    
    }
    if(step == Steps.ENTER_EPSILON) {
        if(currentRule < 0) {
            highlightRow(helperFirstEpsilon);
            instruction("Click the arrow button next to rule " + helperFirstEpsilon);
        }
        else {
            console.log("Really? They can't find the right row??");
        }
    }
}            
function instruction(msg){
    setCell(messageTableId,0,1,msg);
    sayIt(msg);
}

function instructionCont(msg){
    setCell(messageTableId,0,1,getCellValue(messageTableId,0,1,msg) + "<BR>" + msg);
    sayIt(msg);
}

// Create a sting for the First of a nonTerminal
function first(nonTerminal){
    return "First(" + nonTerminal + ")"
}

function follow(nonTerminal){
    return "Follow(" + nonTerminal + ")"
}

function getCellColor(grammerTable, x,y) {
    var myTable = document.getElementById(grammerTable); 
    return myTable.rows[y].cells[x].style.backgroundColor;            
}

function getRowNum(nonTerminal){
    for(let y=0; y< nonTerminalsLength; y++) {
        if(nonTerminals[y].localeCompare(nonTerminal) == 0)
            return y;
    }
    return 0; // Should give an error message
}

function getRowOfTerminal(nontermial) {
    for(let y=1; y< nonTerminalsLength; y++) {
        if (0 == nontermial.localeCompare(getCellValue(firstTable, 0,y))) return y;
    }
    return -1;
}


function cellEmpty(tableId, x,y){
    let button = getCellChild(tableId, x, y);
    return (button.innerHTML.localeCompare(emptyCell) == 0);
}

// Warning if you are in step ENTER_EPSILON_FROM_EPSILON or before, it might not be set yet.
function canBeEpsilon(nontermial){  //////////////////////////////Is this a duplicate function?????????????????????????
    if(nonTerminals.indexOf(grammar[currentRule][1]) == -1) {return false;} // This is not even a nonTerminal
    let button = getButtonAt(firstTable, epsilon, nontermial); 
    return (button.innerHTML.localeCompare(emptyCell) != 0);
}

// Get the column with terminal in location 0.
function getX(tableId, terminal){
    let maxX = document.getElementById(tableId).rows[0].cells.length;
    for(let x=1; x< maxX; x++) {            
        if(getCellValue(tableId, x,0).localeCompare(terminal) == 0) return x;
    }
alert("ERROR: Terminal not found " + terminal);    
    return 0;
}

function isGrammarRuleComplete(y){
    if (y < 0) return true;
    return grammarRuleComplete[y];
}

// Get the row with nontermial in location 0.
function getY(tableId, nontermial){
    let maxY = document.getElementById(tableId).rows.length;
    let y;
    for(y=1; y< maxY; y++) {
        if(getCellValue(tableId, 0,y).localeCompare(nontermial) == 0) return y;
    }    
    alert("ERROR: NonTerminal not found " + nontermial);        
    return 0;
}
function getButtonAt(tableId, terminal,nontermial){
    return getCellChild(tableId, getX(tableId, terminal),getY(tableId, nontermial));
}
function setNode(tableId, x,y, newValue){
    // Get the Cell
    var button = getCellChild(tableId, x,y);
    if(
        (emptyCell.localeCompare(button.innerHTML) != 0) && 
        ((""+newValue).localeCompare(button.innerHTML) != 0) && 
        ((""+newValue).localeCompare(emptyCell) != 0)
    ) {
        instruction("Error: We are about to put a second value in the same box. This grammar is not LL(1) parsable.");
        alert("Error: We are about to put a second value in the same box. This grammar is not LL(1) parsable.");
    }
    button.innerHTML = newValue;
}

function setNodeColor(tableId, x,y, newColor){
    // DEBUG Make sure it is not already set to anther non-. value.
    var button = getCellChild(tableId, x,y);
    button.style.background= newColor;
}



function disableHighlightRow(){
    for(let x=0; x< grammarLength; x++) {
    if(grammarRuleComplete[x]) {
        setCellColor(grammerTable, 0,x, disableColor);
        setCellColor(grammerTable, 1,x, disableColor);
        setCellColor(grammerTable, 2,x, disableColor);
    }
    else{
        setCellColor(grammerTable, 0,x, defaultColor);
        setCellColor(grammerTable, 1,x, defaultColor);
        setCellColor(grammerTable, 2,x, defaultColor);                
    }
    }            
}

function resetHighlightRow(){
    //var button = getCellChild(grammerTable, 0,y);
    //button.style.background= "yellow";
    for(let x=0; x< grammarLength; x++) {
        setCellColor(grammerTable, 0,x, defaultColor);
        setCellColor(grammerTable, 1,x, defaultColor);
        setCellColor(grammerTable, 2,x, defaultColor);               
    }            
}            

function highlightRow(y){
    setCellColor(grammerTable, 0,y, highlightColor);
    setCellColor(grammerTable, 1,y, highlightColor);
    setCellColor(grammerTable, 2,y, highlightColor);
}


function rowIsNullable(y){
    if(isNonTerminalNull(grammar[y][0])) return false; // Already NULL
    for(let x=1; x<grammar[y].length; x++){
        if(!isNonTerminalNull(grammar[y][x])) {return false;}
    }    
    return true;                
}


// We are simplifying the firsts
function highlightFirstTable(){
    let found = false;
    for(let y=1; y< nonTerminalsLength; y++) {
        for(let x=1; x< terminalsLength; x++) {
            setCellColor(firstTable, x ,y, "white");
        }
    }
    if(updateValue < 0) return true;
    for(let x=1; x< terminalsLength; x++) {
        var button = getCellChild(firstTable, x,toRow);
        if(!cellEmpty(firstTable, x,fromRow) && button.innerHTML.localeCompare(updateValue)!=0){
            setCellColor(firstTable, x ,fromRow, "yellow");
            setCellColor(firstTable, x ,toRow, accentColor);
            found = true;
        }
    }
    return found;
}

// We are simplifying the firsts
function highlightFollowTableFirsts(){
    let found = false;
    for(let y=1; y< nonTerminalsLength; y++) {
        let x = 1;
        for(; x< terminalsLength - 1 ; x++) {
            setCellColor(followTable, x ,y, "white");
        }
        for(; x< terminalsLength + nonTerminalsLength - 1 ; x++) {
            if(!cellEmpty(followTable, x,fromRow) && button.innerHTML.localeCompare(updateValue)!=0){
                setCellColor(followTable, x ,y, accentColor);
                found = true;
            }
            else {
                setCellColor(followTable, x ,y, "white");
            }
        }                    
        for(; x< terminalsLength + nonTerminalsLength + nonTerminalsLength - 1 ; x++) {
            setCellColor(followTable, x ,y, "gray");
        }                    
    }
    return found;
}            

function appendNonTerminal(newTerm) {        
    if(nonTerminals.indexOf(newTerm) == -1)
        nonTerminals.push(newTerm);
}

function appendTerminal(newTerm, endOK = false) {
    //console.log(newTerm);
    if((nonTerminals.indexOf(newTerm) == -1) && (terminals.indexOf(newTerm) == -1) && (endOK || newTerm.localeCompare("$") != 0) && newTerm.localeCompare(epsilon) != 0) {
        terminals.push(newTerm);
    }
}    

////////////////////////////////////////////////////////////

function isNonTerminalNull(nontermial) { ////////////////// Is this a duplicate of canBeEpsilon
    if(epsilon.localeCompare(nontermial) == 0) { // It is literally epsilon
        return true;
    }
    if(step == Steps.ENTER_EPSILON || step == Steps.ENTER_EPSILON_FROM_EPSILON){ // It can be made epsilon
        //return canBeEpsilon(nontermial);
        let thisrow = getRowOfTerminal(nontermial); 
        console.log("IsNonTerminalNull: " + " nonterminal: " + nontermial, + "  thisrow: " + thisrow)
        if(thisrow > -1){
            return(emptyCell.localeCompare(getCellChild(firstTable, epsilonCol,thisrow).innerHTML) != 0);
        }
    }
    return false;
}

function arrayToString(index, input) {
    let inputLenght = input.length;
    let output = input[0];
    output = output.concat(" ::=");
    for(let q=1; q< inputLenght; q++) {
        output = output.concat(" "); 
        let isNull = isNonTerminalNull(input[q]);
        
        if(isNull) output = output.concat("<p style=\"color:"+nulledNonTerminalColor+"; display:inline;\" >");
        output = output.concat(input[q]);
        if(isNull)output = output.concat("</p>");
    }
    return output;
}

//////////////////  Step 0, The user just pressed Random or =>

function fillGrammarTableRules() { // Fill in the last column in the GrammarTable (top right). This allows us to show nulled rows
    for(let y=0; y< grammarLength; y++) {
        setCell(grammerTable,2,y,arrayToString(y, grammar[y]));
    }
}

function createGrammarTable(target, grammerTable, tableCols, tableRows) { // Create the table in the top right that holds the grammar 
        deleteMyTable(grammerTable);
        var x = document.createElement("TABLE");
        x.setAttribute("id", grammerTable);
        //document.body.appendChild(x);
        target.appendChild(x);

        var y
        for(y=0; y< tableRows; y++) {
            var newRow = document.createElement("TR");
            newRow.setAttribute("id", "myTr");
            document.getElementById(grammerTable).appendChild(newRow);
            
            var i;
            for(i=0; i< tableCols; i++) {
                var z = document.createElement("TD");
                z.style["width"] = "32px";
                var t = document.createTextNode(" ");
                z.appendChild(t);
                //z.setAttribute("border", "1px solid black");
                //document.getElementById("myTr").appendChild(z);
                newRow.appendChild(z);
            }
        }
}

function userGrammar() {
    let inputStr = document.getElementById("UserGrammar").value;
    let tmp = inputStr.trim().split(" ");
    buildGrammarFrom("S ::= " + tmp[0] + " $ " + inputStr);
}

function randomGrammar() {

    let randomGrammars = [
        //"S ::= A $ " + "A ::= R D " + "D ::= + R D " + "D ::= " + epsilon + " R ::= C B " + "B ::= * C B " + "B ::= / C B " + "B ::= " + epsilon + " C ::= num " + "C ::= ( A )"
            "A ::= R D \n" + "D ::= + R D \n" + "D ::= " + epsilon + " \nR ::= B C \n" + "B ::= * C B \n" + "B ::= / C B \n" + "B ::= " + epsilon + " \nC ::= num \n" + "C ::= ( A )"
    ];
    //buildGrammarFrom(randomGrammar[Math.floor(Math.random()*randomGrammar.length)]);
    let location = Math.floor(Math.random()*randomGrammar.length);        
    //console.log("Location " + location);    
    document.getElementById("UserGrammar").value = randomGrammars[location];
    userGrammar();                
    //buildGrammarFrom(randomGrammars[location]);    
                    
}

function buildGrammarFrom(inputString){
    let tmp = inputString.replace(/(\r\n|\n|\r)/gm, " "); // remove line breaks, etc.
    tmp = tmp.replace(/\s\s+/g, ' '); // Condense multiple spaces into a single space
    tmp = tmp.trim().split(" "); // break the string at the spaces
    grammar = [];
    ruleNum = -1;
    for (let i = 0; i < tmp.length; i++) {
        if(i < tmp.length - 1 && tmp[i+1].localeCompare("::=") == 0){
            ruleNum++;
            grammar[ruleNum] = new Array();
        }
        if(tmp[i].localeCompare("::=") == 0){
            continue;
        }
        //console.log(tmp[i]);
        if(ruleNum < 0){
            alert("Invalid Grammar!");
            return;
        }
        grammar[ruleNum].push(tmp[i].trim()); 
    }
    createTerminals();
    step = Steps.ENTER_EPSILON;
    checkProgress();
}

function createTerminals() {
    const userGrammar = document.getElementById("MyGrammar");
    grammarLength = grammar.length;
    createGrammarTable(userGrammar, grammerTable, 3, grammarLength);
    appendNonTerminal(" "); ////////////////////// Blank at the top so the indexes match
    for(let y=0; y < grammarLength; y++) {
        setCellWidth(grammerTable, 0,y, "1px");
        setCellAsButtonTable(grammerTable, 0,y, "->");
        setCellWidth(grammerTable, 1,y, "1px");
        setCell(grammerTable,1,y,y);
        appendNonTerminal(grammar[y][0]); 
        grammarRuleComplete.push(false);
    }

    for(let y=0; y< grammarLength; y++) {
        for(let q=1; q < grammar[y].length; q++) {
            appendTerminal(grammar[y][q]); 
            nonTerminalFirstRowComplete.push(false);
            nonTerminalFollowRowComplete.push(false);
        }
    }

    appendTerminal("$", true);
    nonTerminalsLength = nonTerminals.length;
    terminalsLength = terminals.length;
    instruction("Select the rules that allow Epsilon in the Grammar table, then select the correct row in the First table");

    createFirstTable();
    fillGrammarTableRules(); // Note: Create the First Table first, so the epsilons are set
}

function h1(text, id) {
    let old = document.getElementById(id)
    if(old) {
        old.remove();
    }
    let h1 = document.createElement('h1');
    h1.setAttribute("id", id);
    h1.appendChild(document.createTextNode(text));
    document.body.appendChild(h1);
}

function createFirstTable() {
    h1("First", "firstID");

    currentX = 0;
    epsilonCol = terminalsLength + nonTerminalsLength;
    createTable(firstTable, epsilonCol+1, nonTerminalsLength);
    //setCell(firstTable,epsilonCol-1,0,"$");
    setCell(firstTable,epsilonCol,0,epsilon);
    for(let y=1; y< nonTerminalsLength; y++) {
        setCell(firstTable,0,y,nonTerminals[y]);
    }
    for(let y=0; y< terminalsLength; y++) {
        setCell(firstTable,y+1,0,terminals[y]);
    }

    for(let y=0; y< nonTerminalsLength-1; y++) {
        setCell(firstTable,y+terminalsLength+1,0,first(nonTerminals[y+1]));
    }
    
    for(let x=1; x < epsilonCol + 1; x++) {
        for(let y=1; y < nonTerminalsLength; y++) {
            setCellAsButtonTable(firstTable, x,y, emptyCell);
        }
    }           
}

function createFollowTable() {

    h1("Follow", "followID");
    
    for(let y=0; y< nonTerminalsLength-1; y++) { // Hide the no longer needed columns in the first table
        show_hide_column(firstTable, y+terminalsLength+1, false );
    }
    
    currentX = 0;
    createTable(followTable, terminalsLength+2*nonTerminalsLength-1, nonTerminalsLength);
    for(let y=1; y< nonTerminalsLength; y++) {
        setCell(followTable,0,y,nonTerminals[y]);
    }
    for(let y=0; y< terminalsLength; y++) {
        setCell(followTable,y+1,0,terminals[y]);
    }

    for(let y=0; y< nonTerminalsLength-1; y++) {
        setCell(followTable,y+terminalsLength+1,0,first(nonTerminals[y+1]));
        setCell(followTable,y+terminalsLength+nonTerminalsLength,0,follow(nonTerminals[y+1]));
    }
    
    for(let x=1; x < terminalsLength+2*nonTerminalsLength-1; x++) {
        for(let y=1; y < nonTerminalsLength; y++) {
            setCellAsButtonTable(followTable, x,y, emptyCell);
        }
    }
    checkProgress();
    
}

/////////////Main Loop check Progress////////////////////////////////////////////////////////            
function checkProgress() {
    resetHelpMe();
    let lastStep = step;
    var done = true;
    if(step == Steps.INVALID) {
        step = Steps.ENTER_Grammar;
        /////////////DEBUG Rest the board.
    }
    if(step == Steps.ENTER_Grammar) {
            // Do nothing. Go to the next step by pressing the Random button or the => button
    }
    if(step == Steps.ENTER_EPSILON) {
        helperFirstEpsilon = -1;
        console.log(grammar);
        for(let y=0; y< grammarLength; y++) {
            var button = getCellChild(firstTable, epsilonCol,getRowNum(grammar[y][0]));
            console.log("Comparing " + grammar[y][1] + " and " + button.innerHTML);
            // Check if all the epsilon values have been filled
            if((grammar[y][1] == epsilon) && (button.innerHTML.localeCompare(emptyCell)==0)){
                done = false;
                helperFirstEpsilon = y;
                console.log("We are not done!");
            }
        }
        // All Explicit epsilon rules have been set
        if(done) {
            console.log("Step 2");
            step = Steps.ENTER_EPSILON_FROM_EPSILON;
            currentRule = -1;
            for(let y=0; y< grammarLength; y++) {
                if(grammar[y][1].localeCompare(epsilon) == 0)
                {
                    grammarRuleComplete[y] = true;
                }
                else {
                    grammarRuleComplete[y] = false;
                }
            }
            console.log("grammarRuleComplete :" + grammarRuleComplete)
            grammarRuleComplete[0] = true;
            disableHighlightRow();
            instruction("Click on a rule in the grammar then select the elements in the First Table it refers to.");

        }
    }
    if(step >= Steps.ENTER_EPSILON_FROM_EPSILON) { ///////////////////////////DEBUG Am I sure???
        for(let y=0; y< grammarLength; y++) {
            if(grammar[y][1].localeCompare(epsilon) == 0)
            {
                grammarRuleComplete[y] = true;
            }
            //else {
                //grammarRuleComplete[y] = false;
            //}
        }    
        disableHighlightRow();                    
    }
    if(step == Steps.ENTER_EPSILON_FROM_EPSILON) {
        done = true;
        for(let y=0; y< grammarLength && done; y++) {
            let thisRowNullable = !isNonTerminalNull(grammar[y][0]); // If it is already NULL, ignore it.
            for(let x=1; x<grammar[y].length && thisRowNullable; x++){
                if(!isNonTerminalNull(grammar[y][x])) {thisRowNullable = false; /*grammar[y][0];*/}
                console.log("Checking "+ y + " at " + x + " " + grammar[y][x] + " " + isNonTerminalNull(grammar[y][x]));
            }
            //grammar[y][0];
            
            if(thisRowNullable) {done = false;} 
            console.log("Checking "+ y);
            if(done) {console.log("Checking "+ y + " done.");} 
            //For every item on the right, if it is a terminal, and it can be NULL, the whole thing can be NULL. 
        }
        if(done){
            step = Steps.FIND_FIRSTS; /////// DEBUG Finish me
            currentRule = -1;
        }
    }
    if(step == Steps.FIND_FIRSTS) {
        done = true;
        for(let y=0; y< grammarLength; y++) {
            if(grammarRuleComplete[y] == false)
            {
                done = false;
            }
        }
        if(done) {
            step = Steps.FIND_FIRSTS_COMPUTED;
            instruction("Well done! Now click a filled in rule that is a First() in the First table");
        }
    }
    let redFound = false;
    if(step == Steps.FIND_FIRSTS_COMPUTED) {                    
        done = true;
        // Eliminate self recursion
        firststep = FirstSteps.SELF_RECURSIVE;
        let offset = terminalsLength; //getX(firstTable, first(grammar[1][0])) - 1;
        for(let y=1; y< nonTerminalsLength; y++) {
            var button = getCellChild(firstTable, y+offset ,y);
            if(button.innerHTML.localeCompare(emptyCell)==0){
                setCellColor(firstTable, y+offset ,y, "gray");
            }
            else
            {
                setCellColor(firstTable, y+offset ,y, "yellow");
                instruction("Eliminate the self recursive cells highlighted in yellow");
                done = false;
            }                        
        }
        if(done) { // Eliminate simple completes
            firststep = FirstSteps.SIMPLE;
            done = true;
            for(let y=1; y< nonTerminalsLength; y++) {
                nonTerminalFirstRowComplete[y] = true;
                for(let x=1; x< nonTerminalsLength; x++) {
                    var button = getCellChild(firstTable, x+offset ,y);
                    if(button.innerHTML.localeCompare(emptyCell)!=0){
                        nonTerminalFirstRowComplete[y] = false;
                        done = false;
                    }                                
                }
            }
            
            for(let y=1; y< nonTerminalsLength; y++) {
                for(let x=1; x< nonTerminalsLength; x++) {
                    if(nonTerminalFirstRowComplete[y]){
                        var button = getCellChild(firstTable, y+offset ,x);
                        if(button.innerHTML.localeCompare(emptyCell)!=0){
                            
                            redFound = true;
                            setCellColor(firstTable, y+offset ,x, accentColor);
                        }
                        else {
                            setCellColor(firstTable, y+offset ,x, "yellow");
                        }
                    }
                }
            }
            if(redFound){
                instruction("Pick any cell highlighted in red");
            }
            for(let y=1; y< nonTerminalsLength; y++) {
                for(let x=1; x< nonTerminalsLength; x++) {
                    if(nonTerminalFirstRowComplete[y]){
                        setCellColor(firstTable, x+offset ,y, "gray");
                    }
                }
            }
        }
        if(done) { // Eliminate Cycles
        //////////////////DEBUG Finish Me if this is possible
        }
        if(done) {         
//console.log("Steps.FIND_FOLLOWS;");                    
            step = Steps.FIND_FOLLOWS;
            for(let y=0; y< grammarLength; y++) {
                if(grammar[y][1].localeCompare(epsilon) == 0)
                {
                    grammarRuleComplete[y] = true;
                }
                else {
                    grammarRuleComplete[y] = false;
//console.log("Steps.FIND_FOLLOWS; false: " +y);
                }
            }
            currentRule = -1;
            //grammarRuleComplete[0] = true;
            disableHighlightRow();
            createFollowTable();                            
        //////////////////DEBUG Finish Me
        }
    }
    if(step == Steps.FIND_FOLLOWS) {
        done = true;
        for(let y=0; y< grammarLength; y++) {            
            if(grammarRuleComplete[y] == false)
            {
                done = false;
            }
        }
        if(done) {
            step = Steps.FIND_FOLLOWS_COMPUTED_FIRSTS;
            for(let y=0; y< grammarLength; y++) {                
                grammarRuleComplete[y] = false;
            }
            instruction("Well done! Now pick any First in the Follows table");
        }                
    }
    if(step == Steps.FIND_FOLLOWS_COMPUTED_FIRSTS) {    
        done = true;
        for(let y=0; y< grammarLength; y++) {            
            if(grammarRuleComplete[y] == false)
            {
                done = false;
            }
        }
        if(done) {
            step = Steps.FIND_FOLLOWS_COMPUTED_FOLLOWS;
            for(let y=0; y< grammarLength; y++) {                
                grammarRuleComplete[y] = false;
            }
            instruction("Well done! Now ...");
        }
    }
    if(step == Steps.FIND_FOLLOWS_COMPUTED_FOLLOWS) { /////////////////////////Simplify the Follows Sets to terminals
        done = true;
        for(let y=0; y< grammarLength; y++) {            
            if(grammarRuleComplete[y] == false)
            {
                done = false;
            }
        }
        if(done) {
            step = Steps.DONE;
            for(let y=0; y< grammarLength; y++) {                
                grammarRuleComplete[y] = false;
            }
            instruction("Well done! Now ...");
        }
    }    
    if(lastStep != step){
        const currentStep = document.getElementById("MyCurrentStep");
        currentStep.innerHTML = "Step " + step + ": " + StepsDescriptive[step] ;
        instruction("Now " + StepsDescriptive[step]);
        if(step == Steps.FIND_FIRSTS_COMPUTED && redFound) {
            instructionCont("Pick any cell highlighted in red");
        }
    }
}

/////////////Main Loop execute Cell////////////////////////////////////////////////////////            

var followRuleX = -1;
var followRuleY = -1;
// Grammar table Button(s) Callback function
function executeCell(table, x,y) {
    console.log("executeCell " + step +":"+table+":"+x+":"+y);
    // Check if we are in the first two steps
    if(step == Steps.ENTER_EPSILON || step == Steps.ENTER_EPSILON_FROM_EPSILON) ///////////////////////////////////Epsilons
    {
        // The Grammar Table in the top Right
        if(table == grammerTable) {
            resetHighlightRow();
            // Check if cell contains EPSILON
            if(step == Steps.ENTER_EPSILON && grammar[y][1] != epsilon) {
                instruction("You need to choose a row with an epsilon");
                disableHighlightRow();
                currentRule = -1;
            }
            else if(step == Steps.ENTER_EPSILON_FROM_EPSILON && !rowIsNullable(y)){
                instruction("You need to choose a row with all nullable nonterminals");
                disableHighlightRow();
                currentRule = -1;
            }
            // In step 1 and epsilon has been chosen
            else {
                instruction("Now choose the proper row in the First table.");
                disableHighlightRow();
                highlightRow(y);
                currentRule = y;
            }
            return;
        }
        // A row in Grammar table has not yet been set
        else if(currentRule < 0){
            instruction("You need to choose a row in the Grammar table first");
        }
        // First Table Buttons
        else if(table == firstTable) {
            console.log("CurrentRule: " + currentRule+ "   grammar[currentRule]: " + grammar[currentRule])
            // Check if the First Table Row matches the first symbol in the selected rule
            if(grammar[currentRule][0].localeCompare(getCellValue(table, 0, y)) == 0){
                // Set the firstTable Epsilon column at the rule row to be the matching rule's index
                setNode(firstTable, epsilonCol, y, currentRule);
                // Check if we need to move to the next step
                checkProgress();
                fillGrammarTableRules();
            }
            else
                instruction("You need to choose the row with '" + grammar[currentRule][0] + "' not '" + getCellValue(table, 0,y) + "'" );
        }
        else {
            instruction("You need to choose a row in the First table or the Grammar table.");
        }
        return;
    }
    else if(step == Steps.FIND_FIRSTS) { /////////////////////////Find Firsts from the Grammar
        if(table == grammerTable) {
            disableHighlightRow(); // Disable every row that is complete
            if(isGrammarRuleComplete(y)){
                instruction("Rule "+y+" is complete. Choose another one.");
            }
            else {
                if(currentRule == y){
                }
                else if(currentRule != -1 && !isGrammarRuleComplete(currentRule)){
                    instruction("Let's finish rule "+currentRule+" before we move on.");
                    highlightRow(currentRule);
                }
                else {                               
                    currentRule = y;
                    highlightRow(y);
                }
                
                //console.log("looking for " + grammar[currentRule][1] + " in "  + nonTerminals.toString()); 
                if(terminals.indexOf(grammar[currentRule][1]) == -1){
                    instruction("Put a " + currentRule + " at the intersection of " + grammar[currentRule][0] + " and " + first(grammar[currentRule][1]) + " in the First Table. ")
                    let i = 1;
                    while (i < grammar[currentRule].length -1 && (terminals.indexOf(grammar[currentRule][i]) == -1) && canBeEpsilon(grammar[currentRule][i])) {
                        instructionCont("And since "+grammar[currentRule][i]+" can be NULL, put a " + currentRule + " at the intersection of " + grammar[currentRule][0] + " and " 
                            +((terminals.indexOf(grammar[currentRule][i+1]) == -1) ? first(grammar[currentRule][i+1]): grammar[currentRule][i+1]) 
                            + " in the First Table as well. ")
                        i++;
                    }
                    //if(terminals.indexOf(grammar[currentRule][1]) != -1){
                    //}
                }
                else {
                    instruction("Put a " + currentRule + " at the intersection of " + grammar[currentRule][0] + " and " + grammar[currentRule][1] + " in the First Table.")
                }
            }
        }
        else if(currentRule < 0){
            instruction("You need to choose a row in the Grammar table first");
        }
        else if(table == firstTable) {
            if(grammar[currentRule][0].localeCompare(getCellValue(firstTable,0,y))== 0){ // If we are in the right row of the first table
                let found = false; // Is this a valid cell to update
                let complete = true; // If we updated it, is this row now complete?
                let i = 1;
                /*while (i < grammar[currentRule].length) {
                    //console.log("Checking " + grammar[currentRule][i]);
                    if(terminals.indexOf(grammar[currentRule][i]) == -1){ // This is a nonterminal
                    //console.log("Terminal " + grammar[currentRule][i]);
                            if((first(grammar[currentRule][i]).localeCompare(getCellValue(firstTable, x,0))==0)) {found = true;}
                            if((emptyCell.localeCompare(getButtonAt(firstTable, first(grammar[currentRule][i]), grammar[currentRule][0]).innerHTML)==0)) {
                                if((first(grammar[currentRule][i]).localeCompare(getCellValue(firstTable, x,0))!=0))
                                    complete = false;
                                    console.log("Not Complete " + currentRule);
                            }
                            //if(i>1 && !canBeEpsilon(grammar[currentRule][i-1])) {break;}
                            if(!canBeEpsilon(grammar[currentRule][i])) {break;}
                            i++;
                    }
                    else { // This is a terminal
                        //console.log("Non Terminal " + grammar[currentRule][i]);
                        if((grammar[currentRule][1].localeCompare(getCellValue(firstTable, x,0))==0)) {
                            found = true;
                        }
                        
                        break;
                    }
                }*/
                let currY = getRowNum(grammar[currentRule][0]);
                while (i < grammar[currentRule].length) {
                    let currX = 0;
                    let isTerminal = false;
                    if(terminals.indexOf(grammar[currentRule][i]) == -1){ // This is a nonterminal
                        currX = getX(firstTable, first(grammar[currentRule][i]));
                    }
                    else { // This is a terminal
                        currX = getX(firstTable, grammar[currentRule][i]);
                        isTerminal = true;
                    }
                    if(x==currX && y == currY) {found = true; setNode(firstTable, x,y, currentRule);}
                    
                    let valueAtCell = getCellChild(firstTable, currX, currY).innerHTML;
                    //console.log("Comparing " +valueAtCell + " " + grammar[currentRule][i]);
                    if((""+currentRule).localeCompare(valueAtCell) !=0) {complete = false;}
                    
                    if(isTerminal) {break;}
                    if(!canBeEpsilon(grammar[currentRule][i])) {break;}
                    i++;
                }                    
                
                
                //if(found) {
                //    setNode(firstTable, x,y, currentRule);
                    if(complete){
                        grammarRuleComplete[currentRule] = true;
                        disableHighlightRow();
                        checkProgress();
                        if(step == Steps.FIND_FIRSTS) {
                            instruction("Well done! Now do another rule in the Grammar.");
                            currentRule = -1;
                        }
                    }    
                //}
                
                
            }
            else {
                instructionCont("Select a cell in row " + grammar[currentRule][0] + " in the First table.");
            }
        }
        else {
            instruction("You need to choose a row in the First table or the Grammar table.");
        }
    }
    else if (step == Steps.FIND_FIRSTS_COMPUTED){ ////////////////////// Simplify the First Sets to terminals
        if(table == firstTable) {
            if(firststep == FirstSteps.SELF_RECURSIVE) {
                if(x + terminalsLength == y) { //////////////// DEBUG Not tested
                    setNode(firstTable, x,y, emptyCell);
                }
            }
            else if(firststep == FirstSteps.SIMPLE){
                if(x>terminalsLength){
                    if(cellEmpty(table, x,y))
                    {
                        instruction("You need to choose a cell with a value in it.");
                        updateValue = -1;
                        highlightFirstTable();
                    }
                    else if(accentColor.localeCompare(getCellColor(table, x,y)) != 0) {
                        instruction("Please choose a red cell.");
                        instructionCont("If there are none left, the grammar is not LL1 parsable.");
                        updateValue = -1;
                        highlightFirstTable();
                    }
                    else {
                        toRow = y;
                        fromRow = x-terminalsLength;
                        updateValue = getCellChild(table, x,y).innerHTML;
                        instruction("Set every value in " + getCellValue(table, 0,toRow) + " to " + updateValue+ " if it has a value in " + getCellValue(table, 0,fromRow));
                        highlightFirstTable();
                    }
                }
                else {
                    if(updateValue < 0){
                        instruction("You need to choose a cell with a value in it from the right First() columns first.");
                    }
                    else {
                        var buttonFrom = getCellChild(firstTable, x,fromRow);
                        var buttonTo = getCellChild(firstTable, x,toRow);
                        if(!cellEmpty(firstTable, x,fromRow) && buttonFrom.innerHTML.localeCompare(updateValue)!=0){
                            setNode(firstTable, x,y, updateValue);
                            if(!highlightFirstTable()){
                                setNode(firstTable, fromRow+terminalsLength, y, emptyCell);
                                highlightFirstTable();
                                checkProgress();
                            }
                        }
                    }
                }
            }
        }
        else {
            instruction("You need to choose a cell in the First table.");
        }
    }
    else if(step == Steps.FIND_FOLLOWS) { /////////////////////////Find Follows from the Grammar
//console.log("Steps.FIND_FOLLOWS " + table);                 
        if(table == grammerTable) {
            disableHighlightRow();
            if(isGrammarRuleComplete(y)){
                instruction("Rule "+y+" is complete. Choose another one.");
            }
            else {
                if(currentRule == y){ // do nothing.
                }
                else if(currentRule != -1 && !isGrammarRuleComplete(currentRule)){
                    instruction("Let's finish rule "+currentRule+" before we move on.");
                    highlightRow(currentRule);
                }
                else {                               
                    currentRule = y;
                    highlightRow(y);
                }
                
                //console.log("looking for " + grammar[currentRule][1] + " in "  + nonTerminals.toString()); 
                //if(terminals.indexOf(grammar[currentRule][1]) == -1){                                
                    if(!findNextFollow()){ // If there is nothing left for this rule
                            grammarRuleComplete[currentRule] = true;
                            disableHighlightRow();
                            checkProgress();                        
                    }
                    //if(terminals.indexOf(grammar[currentRule][1]) != -1){
                    //}
                //}
                //else {
                    //instruction("Put a mark at the intersection of " + grammar[currentRule][j] + " and " + grammar[currentRule][0] + " in the Follow Table.");

                //}
            }
        }
        else if(currentRule < 0){
            instruction("You need to choose a row in the Grammar table first");
        }
        else if(table == followTable) {
            if(x==followRuleX && y==followRuleY) {
                setCellColor(followTable, followRuleX, followRuleY, defaultColor);
                setNode(followTable, x, y, "X");
                if(!findNextFollow()){ // If there is nothing left for this rule
                        //grammarRuleComplete[currentRule] = true;
                        //disableHighlightRow();
                        //checkProgress();                        
                }
            }

        } 
        else {
            instruction("You need to choose a row in the Follow table or the Grammar table.");
        }                
    }
    else if(step == Steps.FIND_FOLLOWS_COMPUTED_FIRSTS) { /////////////////////////Simplify the Follows Sets to terminals
    }    
    else if(step == Steps.FIND_FOLLOWS_COMPUTED_FIRSTS) { /////////////////////////Simplify the Follows Sets to terminals
    }                    
}
function findNextFollow(silent = false) { ///////////// DEBUG Silent added in case I want to do an inital check.
    if(currentRule == -1)
    {
        if(!silent) instruction("Choose a rule in the grammar table");
        return true;
    }
    let i = 1;
    let j = 1;
    while (j < grammar[currentRule].length -1) { 
        console.log("Looking at " + currentRule + ":" + j);                
        if(terminals.indexOf(grammar[currentRule][j]) == -1) {
            i = j+1;
            while (i < grammar[currentRule].length){
            console.log("Looking at " + currentRule + ":" + j + ":" + i);                            
                if(terminals.indexOf(grammar[currentRule][i]) == -1) { // Not a terminal
                    followRuleY = getRowNum(grammar[currentRule][j]);
                    followRuleX = getRowNum(grammar[currentRule][i]) + terminalsLength;
                    if(cellEmpty(followTable, followRuleX,followRuleY)) {
                        if(!silent) instruction("Put a mark at the intersection of " + grammar[currentRule][0] + " and " + first(grammar[currentRule][j]) + " in the Follow Table. ");
                        if(!silent) setCellColor(followTable, followRuleX, followRuleY, highlightColor);
                        console.log("last inner rule " + currentRule + ":" + j + ":" + i);                      
                        return true; // There is stuff left to check for this rule.
                    }    
                    if(canBeEpsilon(grammar[currentRule][i])) {
                        i = grammar[currentRule].length + 1; // non-nullable found. Exit this loop.
                    }                                
                }
                else { // we found a terminal
                    i = grammar[currentRule].length + 1; // terminal found. Exit this loop.
                }
                i++;
            }
            //while (i < grammar[currentRule].length -1 && (terminals.indexOf(grammar[currentRule][i]) == -1) && canBeEpsilon(grammar[currentRule][i])) {
            //    instructionCont("And since "+grammar[currentRule][i]+" can be NULL, put a " + currentRule + " at the intersection of " + grammar[currentRule][0] + " and " 
            //     +((terminals.indexOf(grammar[currentRule][i+1]) == -1) ? first(grammar[currentRule][i+1]): grammar[currentRule][i+1]) 
            //     + " in the First Table as well. ")
            //    i++;
            //}
        }
        j++;
    }
    if(terminals.indexOf(grammar[currentRule][j]) == -1){ // If it does not end in a terminal
        
        followRuleY = getRowNum(grammar[currentRule][j]);
        followRuleX = getRowNum(grammar[currentRule][0]) + terminalsLength + nonTerminalsLength - 1;
        if(cellEmpty(followTable, followRuleX,followRuleY)) {
            if(!silent)instruction("Put a mark at the intersection of " + grammar[currentRule][0] + " and " + follow(grammar[currentRule][j]) + " in the Follow Table. ");
            if(!silent) setCellColor(followTable, followRuleX, followRuleY, highlightColor);
            console.log("last rule " + currentRule);                      
            return true;
        }                      
    }
    console.log("all done " + currentRule);    
    grammarRuleComplete[currentRule] = true;
    disableHighlightRow();
    checkProgress();                                    
    currentRule = -1;
    return false;                
}

function CreateMessageTable() {   
    //createTable(messageTableId, 2,1);
      let myTempTable = document.getElementById(messageTableId); 
      let myTempcell = myTempTable.rows[0].cells[0];
      myTempcell.style.width = '5%'

      if (myTempcell.hasChildNodes()) {
         myTempcell.removeChild(myTempcell.childNodes[0]);
      } 
      let temp = document.createElement('button');
      temp.style.width = '100%'
      temp.innerHTML = "Help";
      temp.onclick = function(){helpMe()};
      myTempcell.appendChild(temp);    
}



