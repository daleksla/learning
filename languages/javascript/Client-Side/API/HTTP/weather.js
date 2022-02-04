/* We can use API's to retrieve data from the internet
 * The fetch() function takes a URL that points to the RESTful API and returns data in a JSON format 
 * In this file, we'll retireve a location, use the 'Open Weather Map' API & display the weather in said location */

document.addEventListener('DOMContentLoaded', async event => {
  console.log('DOMContentLoaded')
  document.querySelector('input').focus()
  document.querySelector('input').addEventListener('keyup', await getLocation) //monitor if something has been entered
})

async function getLocation(event) {
  if(event.key === 'Enter') { //if the key entered is 'Enter'
    const location = event.target.value //get the data entered and store it
    event.target.value = '' //reset the entry to ''
    event.target.select()
    const weather = await getWeather(location) //pass the value entered to function to get the weather
    displayData(weather) //pass weather returned above to a function to display it
  }
}

async function getWeather(location) {
	const base = 'https://api.openweathermap.org/data/2.5/weather'
	const appID = '44c39f3fa462f86b3fc88f5678e5c5ff'
	const url = `${base}?q=${location},uk&appid=${appID}` //url + location inputted + country (uk) + API key
  try {
    const response = await fetch(url) //use the 'fetch' function to get data from website
    if(!response.ok) throw new Error('unMEOWable to make API call') //this error will be thrown to our screen
    return response.json() 
  } catch(err) {
    alert(err.message)
  }
}

function displayData(data) {
  console.log(data)
  document.querySelector('h2').innerText = data.name //print location name determined by API (property name)
  document.querySelector('table tr:nth-child(1) td:nth-child(2)')
    .innerText = data.coord.lon //coordinate longitude property stored on row1, cell2
  document.querySelector('table tr:nth-child(2) td:nth-child(2)')
    .innerText = data.coord.lat //coordinate latitude property stored on row2, cell2
  document.querySelector('table tr:nth-child(3) td:nth-child(2)')
    .innerText = data.main.temp - 273.15 //coordinate latitude property stored on row3, cell2
}


