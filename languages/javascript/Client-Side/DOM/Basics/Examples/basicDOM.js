/* This file usses basic DOM referencing to blank or put a line through text */

document.addEventListener('DOMContentLoaded', event => {
	const buttons = document.querySelectorAll('button')
	const doneButton = getSpecificButton(buttons, 'Done')
	const removeButton = getSpecificButton(buttons, 'Remove')
	doneButton.addEventListener('click', toggleItem)
	removeButton.addEventListener('click', blankItem)
})

function toggleItem()
{
	const text = document.querySelector('p')
	text.classList.toggle('done')
}

function blankItem()
{
	const text = document.querySelector('p')
	text.classList.toggle('blank')
}

function getSpecificButton(myNodeList, text)
{
  for(let i = 0 ; i < myNodeList.length ; i++) 
	{
    if (myNodeList[i].firstChild.nodeValue == text)
		{
      return myNodeList[i]
		}
  }  
}