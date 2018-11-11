open util/integer
open util/boolean 

sig string {}

sig DateTime { 
     day: one Int, 
     month: one Int,
     year: one Int, 
     minute: one Int, 
     second: one Int 
     } {day > 0
	   month > 0 
	   year > 0 
	   minute >= 0 
	   second >= 0}

abstract sig User {
	username: one string,
	email: one string,
	password: one string
	}

sig Location { 
     latitude: one Int, 
     longitude: one Int  
     }{latitude >0 longitude >0}

sig Run { 
     creator: one User, 
     runners: some Individual, 
     spectators: some User,
     beginDate: one DateTime, 
     endDate: one DateTime, 
     numOfPartecipants: one Int, 
     currentPosition: set Location, 
     track: some Location
     } {beginDate != endDate}

sig HealthType { 
     heartbeat: lone Int ,
     bloodPressure: lone Int,
     bloodSugar: lone Int, 
     temperature: lone Int, 
     distance: lone Int, 
     calories: lone Int, 
     steps: lone Int, 
     floors: lone Int 
     } { heartbeat >0 bloodPressure>0 bloodSugar > 0 temperature >0} 


sig Individual extends User { 
   	data: some HealthData, 
   	givesPermissionTo: some ThirdParty,
   	threshold: lone Threshold,
   	additionalInfo: one UserInfo,
   	runSuscribed: some Run 
   	}

sig Threshold {
	value: one Int,
	type: one HealthType
	}

sig UserInfo {	
	dateOfBirth: one string,
	length: one Int,
	weight: one Int,
	gender: one string,
	fiscalCode: one string
	}

sig Group{ 
	components: some Individual, 
	numberOfComponents: one Int, 
	data: some HealthType 
	} {numberOfComponents = #Individual}

sig ThirdParty extends User {  
   	hasPermissionFrom: some Individual, 
   	checkGroup: some Group
   	} 

sig HealthData { 
    	type: one HealthType, 
    	healthStatus: one HealthStatus,
    	value: set Int,
  	located: one Location,
	date: one DateTime,
	ambulanceStatus: one AmbulanceStatus
    	} 

enum HealthStatus { 
	Healthy, 
	InDanger,
	BeingHelped 
	} 

enum AmbulanceStatus {
	Available,
	InTransit,
	Arrived 
} 



/*FACTS*/

fact usernameUnique { 
	//User username is unique
	all disj u1, u2 : User |  u1.username != u2.username
	}
fact emailUnique{
	//User email is unique
	all disj u1, u2: User | u1.email != u2.email
	}

fact healthDataMadeByOnly1Individual{
	//Health data can only be associated with one Individual
	all disj i1, i2: Individual | i1.data & i2.data = none
	}

fact healthDataDoesntExistWithoutIndividual{
	//Health data shall not exist when not associated with an Individual
	all h1: HealthData | one i1: Individual | h1 in i1.data
	}

fact dateTimeDoesntExistWithoutHealthData{
	//DateTime shall not exist when not associated with HealthData
	all d1: DateTime | one h1: HealthData | d1 in h1.date
	}

fact thresholdDoesntExistWithoutHealthType{
	//Thresholds shall not exist when not associated with an HealthType
	all t1: Threshold | one h1: HealthType | t1.type=h1
	}
fact healthTypeDoesntExistWithoutHealthData{
	//HealthType shall not exist when not associated with an HealthData
	all ht1: HealthType | one hd1: HealthData | hd1.type=ht1
	}
fact healthStatusDoesntExistWithoutHealthData{
	//HealthStatus shall not exist when not associated with an HealthData
	all hs1: HealthStatus | one hd1: HealthData | hd1.healthStatus=hs1
	}

fact locationDoesntExistWithoutHealthData{
	//A location shall not exist when not associated with HealthData
	all l1: Location | one h1: HealthData | h1.located=l1
	}

fact differentLocationsCannotHaveSameLongitudeAndLatitude{
	//Two locations can’t be identical
	no disj l1, l2: Location | (l1.latitude = l2.latitude &&
	l1.longitude = l2. longitude)
	}

fact NoOverlappingRuns { 
       //An Individual cannot enroll overlapping runs 
       all disj r1, r2 : Run, i : Individual | r1.beginDate.year = r2.beginDate.year and r1.beginDate.month = r2.beginDate.month and r1.beginDate.day = r2.beginDate.day and
       r1 & r2 in i.runSuscribed  => (r1.beginDate.minute > r2.beginDate.minute and r1.endDate.minute > r2.endDate.minute) 
                                                                                                             or 
                                                   (r1.beginDate.minute < r2.beginDate.minute and r1.endDate.minute < r2.endDate.minute)
       }

fact NoTwoRuns {
	// Not two run in the same place at the same time 
 	all disj r1, r2 : Run | (r1.track != r2.track or r1.beginDate != r2.beginDate or r1.endDate != r2.endDate) 
	} 

fact Permission { 
	//Third part can check data only after permission
	all t: ThirdParty, i: Individual |  t.hasPermissionFrom = i <=> i.givesPermissionTo = t  
	}

fact PermissionGroup {
	//ThirdParty can only request for anonymized data if the number of indivuduals is greater than 1000
	all t: ThirdParty, g: Group | t.checkGroup = g <=> g.numberOfComponents >= 1000 
	} 

fact AmbulanceCalledWhenIndividualInDanger { 
	//Call an ambulance when an Individual is in danger
	all h: HealthData | (h.ambulanceStatus = Available) <=> (h.healthStatus= Healthy) 
     	all h: HealthData | (h.ambulanceStatus = InTransit) <=> (h.healthStatus= InDanger) 
	all h: HealthData | (h.ambulanceStatus = Arrived) <=> (h.healthStatus= BeingHelped) 
     }


fact UserCanRun {
	// A user can participate in a run as a runner or spectator 
	all u: User, r: Run | (u.runSuscribed = r) implies (u in (r.runners + r.spectators)) 
	}

fact onlyHealthyIndividualscanRun { 
	// Only healthy individuals can take part of a run
	all i: Individual, r : Run | i.data.healthStatus != Healthy => i not in r.runners 
	} 



pred show{ 
#User = 5
#Run = 2
#Group = 2 
#UserInfo = 1
} 

run show for 7



 

