package main
// This version does many points, but just one CC iteration each (or a small number).
// So it spends a lot more time on
import (
	"fmt"
	"lp"
	"runtime"
	"time"
	"solver"
	"os"
	"path/filepath"
)

// Global variables
var plinfy float64 // Value of plus infinity
var featol float64 // Feasibility tolerance
var Alpha float64 // Feasibility distance tolerance
var Beta float64  // Movement tolerance
var MaxItns int   // Maximum number of iterations
var MaxSwarmPts int // Maximum number of points in a swarm

//=======================================================================================
func main() {

	// Local variables
	var Status int
	Point := make([]float64, lp.NumCols)
	var ReadDirectory bool

	// Timing variables
	var TotalRunTime time.Duration
	var ModelReadinTime time.Duration
	var CalculationTime time.Duration
	
	// Number of CPUs
	NumCPUs := runtime.NumCPU()
	if solver.PrintLevel > 0 {fmt.Println("\nNumber of logical CPUs:", NumCPUs)}	
	runtime.GOMAXPROCS(NumCPUs)

	// CONTROL PANEL: set parameter values here. TODO: make formal readin and default settings
	plinfy = 1.0e10	// plus infinity for our purposes	
	featol = 1.0e-6	// feasibility tolerance
	var inputMPS string
	//Alpha = 0.001
	//Alpha = 1.0e-8	//smaller than featol so CC success = regular success
	Alpha = 1.0e-6	// If a feasibility distance is smaller than this, the constraint is considered satisfied
	//Beta = 0.001
	//Beta = 1.0e-8	//smaller than featol so CC success = regular success
	Beta = 1.0e-4	// If consensus vector is smaller than this, do something else
	//Beta = 0.1
	MaxItns = 50	// Maximum CC iterations
	//MaxSwarmPts = 2*NumCPUs  // So we only run through 2 jobs per CPU per round
	MaxSwarmPts = NumCPUs
	solver.PrintLevel = 1	// PrintLevel = 0 turns off the printing so you can run through a set of files
	ReadDirectory = false	// true: run through all models in a directory. false: just run one file
	
	if ReadDirectory {
		// Run all of the files in a particular directory
		// Get a list of the files in a directory
		var MPSfiles []string
		MPSfiles, _ = filepath.Glob("c:/chinneck/projects/CCLP/NetlibMPS/TestSetOriginal/*") // change the directory you want to run through
		f, _ := os.Create("c:/chinneck/projects/CCLP/CCLPv6/CCSequentialImpact.txt") // create a summary file to write to. Give it a unique name related to the experiment
		defer f.Close()
		fmt.Fprintln(f,"CCLPv6 50 boxes, killed if 5 in a row no incumbent improvement, no CV projection, CC sequential impact")	// Fill in title of the run
		// List the column titles for the data that gets filled in
		fmt.Fprintln(f,"Model NINF SFD BoxNum ExitPtType ReadTime CalcTime LinProjSucc LinProjTries LinProjImp QuadProjSucc QuadProjTries QuadProjImp IncUpdates",
			"NumIncUpdates0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22",
			"FracIncUpdates0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22")
		
		for i:=0; i< len(MPSfiles); i++ {
			StartTime := time.Now()
			fmt.Println("FILE:",MPSfiles[i])
			Status := lp.ReadMPSFile(MPSfiles[i], plinfy, featol)
			if Status > 0 {
				fmt.Println("  Errors reading MPS file. Aborting this model.")
				continue
			}
			ModelReadinTime = time.Since(StartTime)
			if solver.PrintLevel > 0 {lp.PrintStatistics()}
			CalculationStartTime := time.Now()
			// Scale the model
			//lp.ScaleColumns()
			//lp.ScaleRows()
			// Call the solver
			Point, Status = solver.Solve(Alpha, Beta, MaxItns, MaxSwarmPts, plinfy, featol)
			Point[0]=Point[0]+0.0 //Needed so value is used. Can later print out the point if needed.			
			// Determine total time and Calculation time
			CalculationTime = time.Since(CalculationStartTime)
			TotalRunTime = time.Since(StartTime)
			fmt.Fprintln(f, MPSfiles[i],solver.IncumbentNINF,solver.IncumbentSFD,solver.FinalBox,solver.FinalPointType,
				ModelReadinTime.Seconds(),CalculationTime.Seconds(),
				solver.LinProjSucceeds,solver.LinProjSucceeds+solver.LinProjFails,solver.LinProjFrac/float64(solver.LinProjSucceeds),
				solver.QuadProjSucceeds,solver.QuadProjSucceeds+solver.QuadProjFails,solver.QuadProjFrac/float64(solver.QuadProjSucceeds),
				solver.TotUpdates-1, solver.NumUpdate, solver.FracUpdate )
			//solver.WG.Wait()
			fmt.Println("-------------------Finished number", i, "of", len(MPSfiles)-1,"--------------------------------")
			// wipe the model and restart
			// the following wait is not needed if we use the waitgroup method above. 
			time.Sleep(5*time.Second)  // wait a while for any running go routines to finish gracefully
			lp.EmptyMPS() // empty the MPS file so a new one can be read in
		}
		fmt.Println("DONE!")
		os.Exit(0)
	}

	// Just run for one file -------------------------------------------------

	// Read in the MPS file
	inputMPS = "c:/chinneck/projects/CCLP/NetlibMPS/AllModelsOriginal/25fv47.mps"  // Location of the single file to solve
	fmt.Println("Model:",inputMPS)
	StartTime := time.Now()
	Status = lp.ReadMPSFile(inputMPS, plinfy, featol)
	if Status > 0 {
		fmt.Println("Errors reading MPS file: exiting main program.")
		return
	}
	//lp.ScaleColumns()
	//lp.ScaleRows()
	ModelReadinTime = time.Since(StartTime)
	CalculationStartTime := time.Now()
	
	//test: print out the LP statistics
	if solver.PrintLevel > 0 {lp.PrintStatistics()}
		
	// Call the solver
	Point, Status = solver.Solve(Alpha, Beta, MaxItns, MaxSwarmPts, plinfy, featol)
	Point[0]=Point[0]+0.0 //Needed so value is used. Can later print out the point if needed.
	if solver.PrintLevel > 0{fmt.Println("\nBack in Main routine...")}
	
	// Determine total time and Calculation time
	CalculationTime = time.Since(CalculationStartTime)
	TotalRunTime = time.Since(StartTime)
	if solver.PrintLevel > 0 {
		fmt.Println()
		fmt.Println(TotalRunTime.Seconds(), "Total Time (s)")
		fmt.Println(ModelReadinTime.Seconds(), "Model Read-in Time (s)")
		fmt.Println(CalculationTime.Seconds(), "Calculation Time (s)")
		fmt.Println()
	
		// Summarize results
		if Status == 0 {
			fmt.Println("Feasible point found.")
		} else {
			fmt.Println("No feasible point found. Incumbent SFD:",solver.IncumbentSFD,"NINF:",solver.IncumbentNINF)
			fmt.Println("Smallest NINF:",solver.SmallestNINF)
		}
		fmt.Println()
		
		// Summarize the results on updating of the incumbent
		for i:=0; i<23; i++ {
			if solver.NumUpdate[i] > 0 {
				solver.FracUpdate[i] = solver.FracUpdate[i]/float64(solver.NumUpdate[i])
			}
		}
		fmt.Println("Total incumbent updates",solver.TotUpdates-1)
		fmt.Println("Incumbent updates:",solver.NumUpdate)
		fmt.Println("Incumbent average fractional improvements:",solver.FracUpdate)
		fmt.Println("\nLinear Projection succeeds",solver.LinProjSucceeds,"of",solver.LinProjSucceeds+solver.LinProjFails,"times (",
		  float64(solver.LinProjSucceeds)/float64(solver.LinProjSucceeds+solver.LinProjFails),")")
		fmt.Println("avg. frac. improvement when succeeds:",solver.LinProjFrac/float64(solver.LinProjSucceeds))
		fmt.Println("\nQuadratic Projection succeeds",solver.QuadProjSucceeds,"of",solver.QuadProjSucceeds+solver.QuadProjFails,"times (",
		  float64(solver.QuadProjSucceeds)/float64(solver.QuadProjSucceeds+solver.QuadProjFails),")")
		fmt.Println("avg. frac. improvement when succeeds:",solver.QuadProjFrac/float64(solver.QuadProjSucceeds))
		
	//	fmt.Println("\nIncumbent changes:")
	//	fmt.Println("  Same:",solver.IncumbentSame)
	//	fmt.Println("  Up:  ",solver.IncumbentUp)
	//	fmt.Println("  Down:",solver.IncumbentDown)	

	}
	fmt.Println("Finished", inputMPS)
	os.Exit(0)

}
