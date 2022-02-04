/* Once we have used the script element to import our JavaScript file, we can import other scripts directly into this using the regular syntax 
 * Note: remember, we need our HTML content to load first - execute modules once the content has loaded (ie. in the DOMContentLoaded event) */

import {uppercase, reverse} from './text.js'

window.addEventListener('DOMContentLoaded', event => {
  console.log('DOMContentLoaded')
  const para = document.querySelector('p') //note: we need our HTML file to load first, so we execute it in the event all the content has loaded
  para.innerText = uppercase(para.innerText)
})

window.addEventListener('load', event => {
  const timing = window.performance.timing
  console.log(timing)
  const time = timing.responseStart - timing.fetchStart
  console.log(`latency: ${time} msec`)
})
