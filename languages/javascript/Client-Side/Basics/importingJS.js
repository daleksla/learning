/* When a user requests a web page they are making an HTTP request for an html file
	 * Therefore, any JavaScript we want to make use of must be imported from in the HTML script 
 * The following code is executed upon use of the HTML file 
	 * In this example, we have created 'event handlers' - they react based on certain events 
 * Note: Most of the time our client-side JavaScript will need to interact with the html on the page therefore we need to run our scripts after the html has loaded
	 * For this reason we often put our fancy client-side code in the DOMContentLoaded event
	 * This way it runs as soon as the html is loaded but without waiting for the other resources such as images */

console.log('IMPORTING MODULE')

window.addEventListener('DOMContentLoaded', event => { //this is an event handler we call 'DOMContentLoaded' - this will be triggered when the HTML file is loaded
  console.log('DOMCONTENTLOADED: the HTML document has been completely loaded and parsed, without waiting for stylesheets, images, and subframes to finish loading')
})

window.addEventListener('load', event => { //this is another event handler called 'load' - this will run after all resources for the page have loaded
  console.log('LOAD: the whole page has loaded, including the stylesheet and image')
})

window.addEventListener('beforeunload', event => { //this event will trigger when we navigate away from the page
  console.log('BEFOREUNLOAD: the window, the document and its resources are about to be unloaded')
})

window.addEventListener('unload', event => { //this will trigger when the HTML is replaced (ie by another page)
  console.log('UNLOAD: the document or a child resource is being unloaded')
})

document.addEventListener('visibilitychange', event => { //this will trigger when the user changes tabs
    if (document.hidden) {
        console.log('Browser tab is hidden')
    } else {
        console.log('Browser tab is visible')
    }
})
