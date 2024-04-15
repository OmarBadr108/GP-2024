
class driver;
	transaction tr;
	mailbox mbx;



	function new(mailbox mbx);
		 this.mbx = mbx;
	endfunction

	task driving_input ();	
		
		repeat(10) begin
			mbx.get(s);
			#10;
		end
		
endclass : driver