package lp

// Reads an MPS file, creates appropriate data structures, and allows
// calculations such as the value of the LHS of a constraint given
// a point.

// Make sure that none of the data values matches a keyword. A favourite
// problem is a RHS set named "RHS", or a bounds set named "BOUNDS"

// Reads only the first bounds set, first RHS set, first Range set

import (
	"bufio"
	"fmt"
	"os"
	"strings"
	"strconv"
	"math"
)

type ELEMENT struct {
	Row   int
	Col   int
	Value float64
}

type COL struct {
	Name   string
	Type   string
	BndUp  float64
	BndLo  float64
	NumEl  int
	ElList []int
	ScaleFactor float64
}

type ROW struct {
	Name   string
	Type   string
	RHSlo float64
	RHSup float64
	NumEl  int
	GradVecLenSq float64 // Length of gradient vector squared
	ElList []int
	ScaleFactor float64
}

type LPOBJ struct { //Linear programming object
	Name    string //Name of the problem
	NumRows int    //Number of rows
	NumCols int    //Number of columns
	Rows    []ROW  //List of rows
	Cols    []COL  //List of columns
	ObjRow  int    //Row number of objective function
}
// Global Variables

var Plinfy, Featol float64
var LP LPOBJ
var EmptyLP LPOBJ
var Element []ELEMENT
var NumElements,NumRows,NumCols int
var NumGRows,NumLRows,NumERows,NumNRows,NumRRows,NumICols,NumRCols,MaxElsInRow,MaxElsInCol int
var TotCons int // total number of binding constraints (equalities count as one, ranges count as two)
var TotBnds int // total number of binding bounds (fixed variables count as one)
var	AvgElsPerRow,AvgElsPerCol float64

//=====================================================================================
func ReadMPSFile(MPSFileLocation string, plinfy float64, featol float64) (Status int) {
	// reads in an MPS file
	
	var NumTokens int
	var MPSLineNum int = 0
	var ReadState int = 0
	var MarkAsInteger bool =false
	var tempRow ROW
	var tempCol COL
	var LastColName string
	var tempElement ELEMENT
	var Found bool
	var NumRHSs int = 0
	var RHSName string
	var NumRanges int = 0
	var RangeName string
	var ihold int
	var NumBoundSets int = 0
	var BoundSetName string
	var realhold, realhold1 float64
	
	Status = 0
	
	//establish the local global variable values
	Plinfy=plinfy
	Featol=featol

	MPSFile, err := os.Open(MPSFileLocation)
	if err != nil {
		fmt.Println("Error: problem opening the MPS file ", MPSFileLocation)
		return 1
	}
	
	//zero out the main MPS data structures in case this is not the first file read
	_ = EmptyMPS()
	
	fmt.Println("Beginning MPS file reading...")
	defer MPSFile.Close()
	MPSReader := bufio.NewReader(MPSFile)

	Token := make([]string, 1)

	// The main file reading loop---------------------------------------------

	LastColName=""
	for {
		MPSLineNum++
		
		//test
		//fmt.Println("Operating on MPS file line number",MPSLineNum)
		
		Line, err := MPSReader.ReadString('\n') //reads in a line
		if err != nil {
			//TODO: stops reading at a newline, so you get an error if there isn't 
			//      a blank line at the end of the file. Should fix this.
			fmt.Println("Error: problem reading line ",MPSLineNum,". Read aborted")
			return 1
		}
		
		//test
		//fmt.Println(Line)
		
		if string(Line[0]) == "*" {continue} // Skip lines with an asterisk in the first column 
		Token = strings.Fields(Line) //splits the line above into a slice of tokens using strings.Fields
		NumTokens = len(Token)
		if NumTokens == 0 {continue}	//skip blank lines
		
		// Take the appropriate action for a new keyword ---------------------------

		switch strings.ToUpper(Token[0]) {

		case "NAME":
			if NumTokens == 1 {
				LP.Name = "NoName"
			} else {
				LP.Name = Token[1]
			}
			ReadState = 0
			continue

		case "ROWS":
			ReadState=1
			continue

		case "COLUMNS":
			ReadState=2
			continue

		case "RHS":
			ReadState=3
			continue

		case "BOUNDS":
			ReadState=4
			continue
			
		case "RANGES": 
			ReadState=5
			continue

		case "ENDATA":
			fmt.Println("ENDATA reached at line",MPSLineNum)
			ReadState=6
		}
		
		if ReadState==6 {break} // Do not read any more lines
		
		if NumTokens > 1 && Token[1]=="'MARKER'" {
			if Token[2]=="'INTORG'" {MarkAsInteger=true}
			if Token[2]=="'INTEND'" {MarkAsInteger=false}
		}
		
		//---------------------------------------------------
		
		switch ReadState {
		
		case 1:  // Reading row names
			LP.NumRows++
			tempRow.Type=Token[0]
			tempRow.Name=Token[1]
			LP.Rows=append(LP.Rows,tempRow)
			//test
			//fmt.Println("Row: ",LP.NumRows," Row type: ", tempRow.Type, " Name: ", tempRow.Name)
			
		case 2: // Reading column data
			tempCol.Name=Token[0]
			if tempCol.Name != LastColName {
				// found a new column
				LP.NumCols++
				tempCol.NumEl = 0
				tempCol.Type="R"
				tempCol.BndUp = plinfy // Initialize upper bound to plus infinity
				tempCol.BndLo = 0.0
				if MarkAsInteger {tempCol.Type="I"}
				//TODO: deal with other types, like binary
				LP.Cols=append(LP.Cols,tempCol)
			}
			LastColName = tempCol.Name
			// add first element given in the line
			Found = false
			for i:=0; i<LP.NumRows; i++ {
				if Token[1] == LP.Rows[i].Name {
					Found=true
					NumElements++
					LP.Rows[i].NumEl++
					tempElement.Col=LP.NumCols-1
					tempElement.Row=i
					tempElement.Value,_ = strconv.ParseFloat(Token[2],64)
					Element=append(Element,tempElement)
					LP.Rows[i].ElList=append(LP.Rows[i].ElList,NumElements-1)
					LP.Cols[LP.NumCols-1].ElList=append(LP.Cols[LP.NumCols-1].ElList,NumElements-1)
					LP.Cols[LP.NumCols-1].NumEl++
				}
			}
			if !Found {
				fmt.Println("Error: cannot find row label ",Token[1],". Aborting at line",MPSLineNum)
				return 1
			}
			// if there is a second element in the line, add it too
			if NumTokens == 5 {
				Found = false
				for i:=0; i<LP.NumRows; i++ {
					if Token[3] == LP.Rows[i].Name {
						Found=true
						NumElements++
						LP.Rows[i].NumEl++
						tempElement.Col=LP.NumCols-1
						tempElement.Row=i
						tempElement.Value,_ = strconv.ParseFloat(Token[4],64)
						Element=append(Element,tempElement)
						LP.Rows[i].ElList=append(LP.Rows[i].ElList,NumElements-1)
						LP.Cols[LP.NumCols-1].ElList=append(LP.Cols[LP.NumCols-1].ElList,NumElements-1)
						LP.Cols[LP.NumCols-1].NumEl++
					}
				}
				if !Found {
					fmt.Println("Error: cannot find row label ",Token[3],". Aborting at line",MPSLineNum)
					return 1
				}
			}
			
		case 3: // Reading RHS values. TODO: allow for multiple RHSs
			// Use only the first RHS
			if NumRHSs == 0 {
				NumRHSs++
				RHSName = Token[0]
			}
			if Token[0] != RHSName {continue} // ignore later RHSs
			Found=false
			for i:=0; i<LP.NumRows;i++ {
				if Token[1]==LP.Rows[i].Name {
					// Found matching row name
					Found=true
					ihold=i
					break
				}
			}
			if !Found {
				fmt.Println("Error: cannot find row label ", Token[1],". Aborting at line",MPSLineNum)
				return 1
			}
			realhold,_=strconv.ParseFloat(Token[2],64)
			switch LP.Rows[ihold].Type {
				case "G":
					LP.Rows[ihold].RHSlo=realhold
					LP.Rows[ihold].RHSup=plinfy
				case "L":
					LP.Rows[ihold].RHSlo=-plinfy
					LP.Rows[ihold].RHSup=realhold
				case "E","N":
					LP.Rows[ihold].RHSlo=realhold
					LP.Rows[ihold].RHSup=realhold
			}
			// If a second RHS is isted on the line, then grab it too
			if NumTokens==5 {
				Found=false
				for i:=0; i<LP.NumRows;i++ {		//TODO: make searches efficient: don't start at beginning
					if Token[3]==LP.Rows[i].Name {
						// Found matching row name
						Found=true
						ihold=i
						break
					}
				}
				if !Found {
					fmt.Println("Error: cannot find row label ", Token[3],". Aborting at line",MPSLineNum)
					return 1
				}
				realhold,_=strconv.ParseFloat(Token[4],64)
				switch LP.Rows[ihold].Type {
					case "G":
						LP.Rows[ihold].RHSlo=realhold
						LP.Rows[ihold].RHSup=plinfy
					case "L":
						LP.Rows[ihold].RHSlo=-plinfy
						LP.Rows[ihold].RHSup=realhold
					case "E","N":
						LP.Rows[ihold].RHSlo=realhold
						LP.Rows[ihold].RHSup=realhold
				}								
			}
			
		case 4: // Reading bounds data. TODO: make it read multiple bounds sets
			if NumBoundSets == 0 {
				// First bound set found
				NumBoundSets++
				BoundSetName = Token[1]
				if Token[0] == "FR" || Token[0] == "PL" || Token[0] == "MI" {
					if NumTokens < 3 {
						fmt.Println("WARNING: too few tokens on MPS file line",MPSLineNum,". Bound set name likely missing.")
					} 
				} else if NumTokens < 4 {
					fmt.Println("WARNING: too few tokens on MPS file line",MPSLineNum,". Bound set name likely missing.")
				}	
			}
			if Token[0] == "FR" || Token[0] == "PL" || Token[0] == "MI" {
				if NumTokens < 3 {
					fmt.Println("WARNING: too few tokens on MPS file line",MPSLineNum,". Bound set name may be missing.")
				} 
			} else if NumTokens < 4 {
				fmt.Println("WARNING: too few tokens on MPS file line",MPSLineNum,". Bound set name may be missing.")
			}			
			
			if Token[1] != BoundSetName {continue} // read only the first bounds set
			// Find the matching column
			Found=false
			for i:=0;i<LP.NumCols;i++ {
				if Token[2]==LP.Cols[i].Name {
					ihold=i
					Found=true
					break
				}
			}
			if !Found {
				fmt.Println("Warning: no match for column name on MPS line ",MPSLineNum,". Continuing...")
				continue
			}
			if Token[0] != "FR" && Token[0] != "PL" && Token[0] != "MI" {realhold,_ = strconv.ParseFloat(Token[3],64)}
			switch Token[0] {
			case "LO":
				LP.Cols[ihold].BndLo = realhold
			case "UP":
				LP.Cols[ihold].BndUp = realhold
			case "FX":
				LP.Cols[ihold].BndLo = realhold
				LP.Cols[ihold].BndUp = realhold
			case "FR":
				LP.Cols[ihold].BndLo = -plinfy
				LP.Cols[ihold].BndUp = plinfy
			case "MI":
				LP.Cols[ihold].BndLo = -plinfy
			case "PL":
				LP.Cols[ihold].BndUp = plinfy
			case "BV":  // Binary variable
				LP.Cols[ihold].Type = "I"
				LP.Cols[ihold].BndLo = 0.0
				LP.Cols[ihold].BndUp = 1.0
			case "LI": // Lower bounded integer variable
				LP.Cols[ihold].Type = "I"
				LP.Cols[ihold].BndLo = realhold
				LP.Cols[ihold].BndUp = plinfy
			case "UI": // Upper bounded integer variable
				LP.Cols[ihold].Type = "I"
				LP.Cols[ihold].BndLo = 0.0
				LP.Cols[ihold].BndUp = realhold
			case "SC": // Semi-continuous variable
				fmt.Println("Warning: only the continuous part of a semi-continuous variable is handled. Lower bound = 1.0.")
				LP.Cols[ihold].BndLo = 1.0
				LP.Cols[ihold].BndUp = realhold
			default:
				fmt.Println("Error: no match for bound type on MPS file line ",MPSLineNum,". Continuing...")
			}
			
			case 5: { //reading RANGES. TODO: make it read multiple ranges.
				if NumRanges == 0 {
					// First range set found
					NumRanges++
					RangeName = Token[1]
				}
				if Token[1] != RangeName {continue} // read only the first range set
				// Find the matching row
				Found=false
				for i:=0;i<LP.NumRows;i++ {
					if Token[1]==LP.Rows[i].Name {
						ihold=i
						Found=true
						break
					}
				}
				if !Found {
					fmt.Println("Warning: no match for row name on MPS line ",MPSLineNum,". Continuing...")
					continue
				}
				realhold,_ = strconv.ParseFloat(Token[2],64)
				realhold1 = realhold	// The sign is needed for E type ranges
				if realhold < 0.0 {realhold = -realhold} // Absolute value is needed in some cases
				switch LP.Rows[ihold].Type {
				case "G":
					LP.Rows[ihold].RHSup = LP.Rows[ihold].RHSlo + realhold
					LP.Rows[ihold].Type="R"
					NumGRows = NumGRows - 1
					NumRRows = NumRRows + 1
				case "L":
					LP.Rows[ihold].RHSlo =  LP.Rows[ihold].RHSup - realhold
					LP.Rows[ihold].Type="R"
					NumLRows = NumLRows - 1
					NumRRows = NumRRows + 1
				case "E":
					if realhold1 > 0.0 {
						LP.Rows[ihold].RHSup = LP.Rows[ihold].RHSlo + realhold
					} else {
						LP.Rows[ihold].RHSlo = LP.Rows[ihold].RHSup - realhold
					}
					LP.Rows[ihold].Type="R"
					NumERows = NumERows - 1
					NumRRows = NumRRows + 1
				} // end of switch on row type
			} // end of switch on case 5
		} // end of switch on ReadState ------------------------------------------
	} // end of main line reading for --------------------------------------------

	// Post-process 
	
	// We take the first nonbinding row as the objective function
	ihold = -1 // initial row of objective function
	for i:=0; i<LP.NumRows; i++ {
		if LP.Rows[i].Type=="N" {
			ihold=i
			break
		}
	}
	if ihold<0 {fmt.Println("Warning: no objective function in model!")}
	LP.ObjRow=ihold
	if ihold>=0 {
		fmt.Println("Objective function:",LP.Rows[ihold].Name)
		if LP.Rows[ihold].RHSlo != 0.0 || LP.Rows[ihold].RHSup != 0.0 {fmt.Println("Warning: objective function includes constant term.")}
	}
	
	// Look for empty rows and columns. Also fill in the initial scale factors
	for i:=0; i<LP.NumRows; i++ {
		LP.Rows[i].ScaleFactor = 1.0
		if LP.Rows[i].NumEl==0 {
			fmt.Println("Warning: row ",i," (",LP.Rows[i].Name,") has no elements. Converted to nonbinding type.")
			LP.Rows[i].Type="N"
		}
	}
	for i:=0; i<LP.NumCols; i++ {
		LP.Cols[i].ScaleFactor = 1.0
		if LP.Cols[i].NumEl == 0 {
			fmt.Println("Error in MPS file: column ",i," (",LP.Cols[i].Name,") has no elements. Aborting.")
		}

	}

	//test
	//fmt.Println("LP: ",LP)
	//fmt.Println("Elements: ", Element)

	fmt.Println("MPS file reading complete.")
	GetStatistics()
	return 0
} // End of ReadMPSFile function

//=========================================================================================================
func ConBodyValue(FuncNum int, Point []float64) (BodyValue float64, Status int) {
	// Calculates the LHS value of the given function
	// Status values. 0:normal, 1:nonbinding, 2:problem.
	
	var icol, ielem int
	var realhold float64
	
	if FuncNum < 0 || FuncNum > LP.NumRows-1 {
		fmt.Println("Error in calculating LHS value: no function number ",FuncNum,".")
		//test
		return 0.0, 2
	}
	
	realhold = 0.0
	for i:=0; i<LP.Rows[FuncNum].NumEl; i++ {
		ielem=LP.Rows[FuncNum].ElList[i]
		icol=Element[ielem].Col
		realhold = realhold + Element[ielem].Value*Point[icol]
	}
	//test
	if math.IsNaN(realhold) {
		//test hhhm there is a problem with NaNs being generated
		fmt.Println("Warning: NaN generated in ConBodyValue routine for function",FuncNum,LP.Rows[FuncNum].Name)
		//test
		realhold = 0.0
		if LP.Rows[FuncNum].NumEl <= 0 {fmt.Println("Number of elements in the row:",LP.Rows[FuncNum].NumEl)}
		for i:=0; i<LP.Rows[FuncNum].NumEl; i++ {
			ielem=LP.Rows[FuncNum].ElList[i]
			icol=Element[ielem].Col
			if math.IsNaN(Element[ielem].Value) {fmt.Println("Element",ielem,"is NaN")}
			if math.IsNaN(Point[icol]) {fmt.Println("Point element",icol,"is NaN")}
			realhold = realhold + Element[ielem].Value*Point[icol]
		}
		fmt.Println("NaN discovered in ConBodyVal for FuncNum",FuncNum,"at input point",Point)
		os.Exit(1)
		// check the input point
		//for i:=0; i<LP.NumCols; i++ {
		//	if Point[i] > Plinfy {fmt.Println("In ConBodyValue point element",i,"is too large:", Point[i])}
		//} 
		return realhold,2
		//check whether anything is funky with the row values or Point values
		//for i:=0; i<LP.Rows[FuncNum].NumEl; i++ {
			//ielem=LP.Rows[FuncNum].ElList[i]
			//icol=Element[ielem].Col
			//fmt.Println("Row:",FuncNum,"Col:",icol,"Coefficient:",Element[ielem].Value,"Col coeff in Point:",Point[icol])
		//}
	}
	if LP.Rows[FuncNum].Type=="N" {return realhold,1}
	return realhold,0
} 
//============================================================================================================
func EmptyMPS() (Status int) {
	// Makes sure the MPS file structures are empty in case a new model is read in
	
	
	for i:=0; i<LP.NumRows; i++ {
		for j:=0; j<LP.Rows[i].NumEl; j++ {
			LP.Rows[i].ElList[j] = 0
		}
		LP.Rows[i].Name=""
		LP.Rows[i].NumEl=0
		LP.Rows[i].RHSlo=0.0
		LP.Rows[i].RHSup=0.0
		LP.Rows[i].Type=""
		LP.Rows[i].GradVecLenSq = 0.0
		LP.Rows[i].ScaleFactor = 1.0
		LP.Rows[i].ElList=nil
	}
	for i:=0; i<LP.NumCols; i++ {
		for j:=0; j<LP.Cols[i].NumEl; j++ {
			LP.Cols[i].ElList[j] = 0
		}
		LP.Cols[i].BndLo=0.0
		LP.Cols[i].BndUp=0.0
		LP.Cols[i].Name=""
		LP.Cols[i].NumEl=0
		LP.Cols[i].Type=""
		LP.Cols[i].ScaleFactor = 1.0
		LP.Cols[i].ElList=nil
	}
	for i:=0; i<NumElements; i++ {
		Element[i].Col = 0
		Element[i].Row = 0
		Element[i].Value = 0.0
	}
	
	LP.Name=""
	LP.NumCols=0
	LP.NumRows=0
	LP.ObjRow=0
	LP.Rows=nil
	LP.Cols=nil
	Element=nil
	LP.ObjRow=0
	
	NumElements=0
	NumRows=0
	NumCols=0
	NumGRows=0; NumLRows=0; NumERows=0; NumNRows=0; NumRRows=0; NumICols=0; NumRCols=0; MaxElsInRow=0; MaxElsInCol=0
	TotCons=0; TotBnds=0;
	AvgElsPerRow=0.0; AvgElsPerCol=0.0 
	
	LP = EmptyLP
	
	return 0
}
//=============================================================================================================
//TODO: might be easier to return a structure
// Calculates various statistics about the LP model, includeing the gradient vector length squared
func GetStatistics() () {
	
	var rhold float64
	
	NumRows=LP.NumRows
	NumCols=LP.NumCols
	
	//test
	//fmt.Println ("In GetStatistics: plinfy is",Plinfy)
	//fmt.Println("In GetStatistics: LP is",LP)
	
	// Recall: NumRows is as reported in MPS; TotCons is number of binding row bounds
	NumGRows=0; NumLRows=0; NumERows=0; NumNRows=0; NumRRows=0; AvgElsPerRow=0; MaxElsInRow=0; TotCons=0
	for i:=0; i<LP.NumRows; i++ {
		switch LP.Rows[i].Type {
		case "G":
			NumGRows++
			if LP.Rows[i].RHSlo > -Plinfy {TotCons++}
		case "L":
			NumLRows++
			if LP.Rows[i].RHSup < Plinfy {TotCons++}
		case "E":
			NumERows++
			TotCons++
		case "R":
			NumRRows++
			// Check that range hasn't been reversed
			if LP.Rows[i].RHSlo > LP.Rows[i].RHSup {
				// row bounds have been reversed, so switch them back
				rhold = LP.Rows[i].RHSlo
				LP.Rows[i].RHSlo = LP.Rows[i].RHSup
				LP.Rows[i].RHSup = rhold
				fmt.Println("Bounds on row",LP.Rows[i].Name,"were reversed: correcting by swapping.")
			}
			if LP.Rows[i].RHSup - LP.Rows[i].RHSlo <= Featol {
				// The range is actually an equality
				NumRRows = NumRRows - 1
				NumERows= NumERows + 1
				LP.Rows[i].Type = "E"
				TotCons++
			} else {
				if LP.Rows[i].RHSlo > - Plinfy {TotCons++}
				if LP.Rows[i].RHSup < Plinfy {TotCons++}
			}
		case "N":
			NumNRows++
		}
		if LP.Rows[i].NumEl > MaxElsInRow {MaxElsInRow = LP.Rows[i].NumEl}
		// Calculate the length of the gradient squared
		rhold=0.0
		for iel:=0; iel<LP.Rows[i].NumEl; iel++ {
			rhold = rhold + Element[LP.Rows[i].ElList[iel]].Value*Element[LP.Rows[i].ElList[iel]].Value
		}
		LP.Rows[i].GradVecLenSq=rhold
	}
	AvgElsPerRow=float64(NumElements)/float64(LP.NumRows)
	
	// Look at columns
	NumICols=0; NumRCols=0; NumICols=0; AvgElsPerCol=0; MaxElsInCol=0; TotBnds=0
	for i:=0; i<LP.NumCols; i++ {
		switch LP.Cols[i].Type {
			case "R":
				NumRCols++
			case "I":
				NumICols++
		}
		if LP.Cols[i].NumEl > MaxElsInCol {MaxElsInCol = LP.Cols[i].NumEl}
		// count the number of actual bounds and switch any reversed bounds
		if LP.Cols[i].BndLo > LP.Cols[i].BndUp{
			// bounds are reversed, so switch them back
			rhold=LP.Cols[i].BndLo
			LP.Cols[i].BndLo = LP.Cols[i].BndUp
			LP.Cols[i].BndUp = rhold
			fmt.Println("Bounds on variable",LP.Cols[i].Name,"were reversed: correcting by swapping.")
		}
		if LP.Cols[i].BndUp - LP.Cols[i].BndLo <= Featol {
			// variable is fixed
			TotBnds++
		} else {
			if LP.Cols[i].BndLo > -Plinfy {TotBnds++}
			if LP.Cols[i].BndUp < Plinfy {TotBnds++}
		}
	}
	AvgElsPerCol=float64(NumElements)/float64(LP.NumCols)
	return
}
//=============================================================================================
func GetLPPointer() (LPPtr *LPOBJ) {
// Returns a pointer to the LP object. Probably not needed since the LP is exposed as a global variable.
	LPPtr = &LP
	return LPPtr
}
//============================================================================================
// Prints out the main statistics
func PrintStatistics() {
	fmt.Println("\nLP STATISTICS:")
	fmt.Println(NumElements, "NONZERO ELEMENTS")
	fmt.Println("  ",AvgElsPerRow, "average elements per row")
	fmt.Println("  ",MaxElsInRow, "maximum elements in a row")
	fmt.Println("  ",AvgElsPerCol, "average elements per column")
	fmt.Println("  ",MaxElsInCol, "maximum elements in a column")
	fmt.Println(NumRows, "ROWS IN TOTAL")
	fmt.Println(TotCons, "Binding row bounds (equalities count as 1)")
	fmt.Println("  ",NumGRows, "GT rows")
	fmt.Println("  ",NumLRows, "LT rows")
	fmt.Println("  ",NumRRows, "range rows")
	fmt.Println("  ",NumERows, "equality rows")
	fmt.Println("  ",NumNRows, "nonbinding rows")
	fmt.Println(NumCols, "COLUMNS IN TOTAL")
	fmt.Println(TotBnds, "Binding column bounds (equalities count as 1)")
	fmt.Println("  ",NumRCols, "real-valued columns")
	fmt.Println("  ",NumICols, "integer columns")
}
//=============================================================================================
// Scale the rows. Initially this is done by dividing through by the largest element
// This is known as equilibriation scaling. Just do a single pass.
func ScaleRows() {
	// Local variables
	var MaxValue, MaxMaxValue, MinValue, MinValueAfter float64
	var iel int
	var rhold float64
	var ScaleApplied bool
	
	ScaleApplied = false
	MaxMaxValue = 0.0; MinValue = Plinfy; MinValueAfter = Plinfy
	for irow:=0; irow<LP.NumRows; irow++ {
		MaxValue = 0.0
		for i:=0; i<LP.Rows[irow].NumEl; i++ {
			iel = LP.Rows[irow].ElList[i]
			rhold = math.Abs(Element[iel].Value)
			if rhold > MaxValue {MaxValue = rhold}
			if rhold < MinValue {MinValue = rhold}
		}
		if MaxValue > MaxMaxValue {MaxMaxValue = MaxValue}
		if MaxValue <= 0.0 || MaxValue == 1.0 {continue}
		
		ScaleApplied = true
		LP.Rows[irow].ScaleFactor = LP.Rows[irow].ScaleFactor * MaxValue // Note scale factor multiplies earlier scale value

		//fmt.Println("Scale factor for row",irow,"is",MaxValue) // to look at row scales
		// Now divide through by the largest element
		rhold = 0.0 //use this to recalculate the length of the vector squared
		for i:=0; i<LP.Rows[irow].NumEl; i++ {
			iel = LP.Rows[irow].ElList[i]
			Element[iel].Value = Element[iel].Value/MaxValue
			rhold = rhold + Element[iel].Value*Element[iel].Value
			if math.Abs(Element[iel].Value) < MinValueAfter {MinValueAfter = math.Abs(Element[iel].Value)}
		}
		LP.Rows[irow].GradVecLenSq = rhold
		// Now check on the RHS values, which may also need to be scaled by the same value
		if LP.Rows[irow].RHSlo > -Plinfy && LP.Rows[irow].RHSlo < Plinfy {
			LP.Rows[irow].RHSlo = LP.Rows[irow].RHSlo / MaxValue
		}
		if LP.Rows[irow].RHSup > -Plinfy && LP.Rows[irow].RHSup < Plinfy {
			LP.Rows[irow].RHSup = LP.Rows[irow].RHSup / MaxValue
		}
	}
	fmt.Println("Before row scaling: minimum A matrix element:",MinValue,"Maximum A matrix value:",MaxMaxValue,"Max/min:",MaxMaxValue/MinValue)
	if ScaleApplied {
		fmt.Println("After row scaling: minimum A matrix element:",MinValueAfter,"Maximum A matrix value: 1.0. Max/min:",1.0/MinValueAfter)
	} else {
		fmt.Println("No row scaling applied.")
	}
	//os.Exit(1)  //useful to kill program if you just want to look at the row scales
	return
}

//=============================================================================================
// Scale the columns. Initially this is done by dividing through by the largest element
// This is known as equilibriation scaling. Just do a single pass.
func ScaleColumns() {
	// Local variables
	var MaxValue, MaxMaxValue, MinValue, MinValueAfter float64
	var iel int
	var rhold float64
	var ScaleApplied bool
	
	ScaleApplied = false
	MaxMaxValue = 0.0; MinValue = Plinfy; MinValueAfter = Plinfy
	for icol:=0; icol<LP.NumCols; icol++ {
		MaxValue = 0.0
		for i:=0; i<LP.Cols[icol].NumEl; i++ {
			iel = LP.Cols[icol].ElList[i]
			rhold = math.Abs(Element[iel].Value)
			if rhold > MaxValue {MaxValue = rhold}
			if rhold < MinValue {MinValue = rhold}
		}
		if MaxValue > MaxMaxValue {MaxMaxValue = MaxValue}
		if MaxValue <= 0.0 || MaxValue == 1.0 {continue}
		
		ScaleApplied = true
		LP.Cols[icol].ScaleFactor = LP.Cols[icol].ScaleFactor * MaxValue // Note scale factor multiplies earlier scale value

		//fmt.Println("Scale factor for row",irow,"is",MaxValue) // to look at row scales
		// Now divide through by the largest element
		for i:=0; i<LP.Cols[icol].NumEl; i++ {
			iel = LP.Cols[icol].ElList[i]
			Element[iel].Value = Element[iel].Value/MaxValue
			if math.Abs(Element[iel].Value) < MinValueAfter {MinValueAfter = math.Abs(Element[iel].Value)}
		}
		// Now check on the column bounds, which may also need to be scaled by the same value
		if LP.Cols[icol].BndLo > -Plinfy && LP.Cols[icol].BndLo < Plinfy {
			LP.Cols[icol].BndLo = LP.Cols[icol].BndLo / MaxValue
		}
		if LP.Cols[icol].BndUp > -Plinfy && LP.Cols[icol].BndUp < Plinfy {
			LP.Cols[icol].BndUp = LP.Cols[icol].BndUp / MaxValue
		}
	}
	//recalculate the row vector lengths squared
	for irow:=0; irow<LP.NumRows; irow++ {
		rhold = 0.0 //use this to recalculate the length of the vector squared
		for i:=0; i<LP.Rows[irow].NumEl; i++ {
			iel = LP.Rows[irow].ElList[i]
			rhold = rhold + Element[iel].Value*Element[iel].Value
		}
		LP.Rows[irow].GradVecLenSq = rhold
	}
		
	fmt.Println("Before column scaling: minimum A matrix element:",MinValue,"Maximum A matrix value:",MaxMaxValue,"Max/min:",MaxMaxValue/MinValue)
	if ScaleApplied {
		fmt.Println("After column scaling: minimum A matrix element:",MinValueAfter,"Maximum A matrix value: 1.0. Max/min:",1.0/MinValueAfter)
	} else {
		fmt.Println("No column Scaling applied.")
	}
	//os.Exit(1)  //useful to kill program if you just want to look at the row scales
	return
}

