/* Here we store the module we wish to import in our 'main.js' file */

export function uppercase(nameArray) {
	const result = []
	for (const name of nameArray) {
		result.push(name.toUpperCase())
	}
	return result.join('')
}

export const reverse = val => val.split('').reverse().join('')
