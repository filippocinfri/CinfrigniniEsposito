// ENTITIES USEFUL

// Name is used to represent a string containing the name of users
sig Name {}

// Posizione is used to define longitude and latitued of a Station
sig Position {}

// Type is used to specify which type of socket is a certain charging socket
sig Type {}

// a boolean to represent if a charging station is free to be used or not
sig Bool {}

// a code used to unlock the charging socket before start the charging
sig Code {}

// an int between 0 and 100
sig Percentage {}

// date and time for the reservation
sig Time {}

// NON USATA an int to measure the max amp-hours of a battery
// sig Capacity {}
// ___________________________________________________




// ENTITIES

// Users of the app have a name
sig User {
	name: one Name,
}

//
sig Operator  extends User {
	cpo: one CPO, // Ogni operatore ha una CPO
}

//
sig CPO {
	name: one Name,
	operators: some Operator,
} {
	#operators > 0	// Ogni CPO ha almeno un operatore
}

//
sig Driver extends User {}

//
sig Station {
	//ID: one id   it is not useful to model
	name: one Name,
	position: one Position,
	sockets: some ChargingSocket,
	batteries: some Battery,
} {
	#sockets >=  1
}

sig ChargingSocket {
	type: one Type,
	//avilable: bool Alloy doesn’t have a native boolean type. There are two ways to emulate this. !!!!!!!!!!!!
	available: one Bool,
	unlocked: one Bool,
	inUse: one Bool, 
	nextCode: lone Code,
}

sig DSO {
	supply: Station,
}

sig Battery {
	percentage: one Percentage,
}

sig Reservation {
	user: one User,	// Ogni reservation ha una e una sola persona e
	socket: one ChargingSocket,	// una sola socket
	station: one Station,
	code: one Code,
	startingTime: one Time,
}
// ___________________________________________________




// FACTS
// In the following are stated in Alloy the facts that must hold for the domain modeled in order to maintain 
// consistency with the real world. For the sake of readability they are stated in alphanumerical order

// All stations are located in a different position
fact stationLocations {
	( all disj s1, s2: Station | s1.position != s2.position )
	and
	(#Position = #Station)
}

// All stations have a battery, the number of batteries in the system is greate than the number of stations
fact stationsHaveBatteries {
	( all s: Station | #s.batteries >= 1 )
	and
	(#Station =< #Battery)
}

// All stations have batteries that no other station has, there can't be shared batteries
fact noSharedBatteries {
	(all disj s1, s2: Station | #(s1.batteries & s2.batteries) = 0)
}

// Socket in uso -> socket non disponibile, soket disponibile -> socket non in uso
fact usingIffNotFree {
	(all c: ChargingSocket | 	c.available != c.inUse) // avialble != in Use
	//and
	//() // available => no nextCode FINIRE
}

// Ogni user è o un Driver o un Operator, nessun tipo di user può essere anche dell'altro tipo
fact userDisjointed {
	(#User = #Operator + #Driver)
	// (#(Operator & Driver) = 0) Warning from analyzer: & is irrelevant because the two subexpressions are always disjoint
}

// In ogni reservation la socket effettivamente appartiene all stazione
fact socketBelongsToStation {
	(all r: Reservation  | #(r.socket - (r.station).sockets) = 0) // la differenza tra la socket e le socket della stazione deve essere vuota
}
// si può scrivere senza cardinalità e con = none ? CONTROLLA


// i code delle reservation sono unici, non possono esserci duplicati
// ogni code nelle reservation ha una socket con un codice corrispondente
fact codeIsUnique {
	(all disj r1, r2: Reservation | r1.code != r2.code)
	and
	(#Reservation < #ChargingSocket)	//non possono esserci più prenotazioni che socket
	and
	(all r: Reservation | 
	one c: ChargingSocket |
	r.code = c.nextCode and r != none and c != none)
}

// same number of time and reservations
fact sameNumTimeReserv {
	( #Time = #Reservation )
}

// Ogni Driver ha al massimo una prenotazione
fact driverHas1ReservAtMost {
	all disjoint r1, r2: Reservation | r1.user != r2.user
}


//____________________________________________________
