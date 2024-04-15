
// function of this class is to generate the random input based on the signals and constraints in the 'transaction' class
// and then pass values to the driver in the mailbox

class generator ;
	transaction tr;

	// creating mailbox to put inputs inside it
	mailbox mbx;

		//mbx = new();  
		// check this allocation //
		 
		function new(mailbox mbx);
		  this.mbx = mbx;
		endfunction

	task input_generation ();	
		
		repeat(10) begin
			tr = new();
			tr.randomize();
			mbx.put(s);
			#10;
		end






	endtask : input_generation

endclass