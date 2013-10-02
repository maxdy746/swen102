// A model of a hotel booking system.
// We record the bookings made for a hotel,
// and also the rooms available on a particular day.

abstract sig RoomType { rate : Int }{ rate > 0 }
sig Double in RoomType {}
sig Single in RoomType {}

sig Room {
  type : RoomType,
  number : Int
}{
  // Only positive numbers.
  number >= 0
  // Every room is in one Hotel.
  one this.~rooms
}

sig Guest {}

sig Booking {
  room: Room,
  guest : Guest,
  startDate, endDate : Int
}{ 
  // Every booking is for one Hotel.
  one this.~bookings
  //TODO: startDate is before endDate
}

sig Hotel {
  rooms : set Room,
  bookings : set Booking,
  calendar : set Day
}{
  // Hotels obviously have some number of rooms, 
  // otherwise it's not really a Hotel!
  some rooms
  // All rooms in a hotel have different numbers.
  all disj r1,r2 : rooms | r1.number = r2.number implies r1 = r2
}

sig Day {
  date: Int,//the date of this day,
            //represented as an Int for simplicity
  occupied : set Room,
  vacant : set Room
}{
  // Every day is in calendar of some Hotel.
  some this.~calendar
}
//my checks

check a {}
check b {}
check c {}
check d {}
check e {}
check f {}
check g {}
check h {}

//my run commands

run i {}
run ii {}
run iii {}
run iv {}

