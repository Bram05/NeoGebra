#version 400 core

out vec4 colour;

in vec2 TexCoords;

uniform vec4 u_Colour;
uniform sampler2D tex;
	
void main()
{   

	
	colour = vec4(u_Colour.xyz + (1.0 - u_Colour.xyz) * (1.0 - abs(texture( tex, TexCoords).r)), 1.0);
	if (texture( tex, TexCoords).r == 0.0) {
		colour = vec4(0.0, 0.0, 0.0, 0.0);
	}
}