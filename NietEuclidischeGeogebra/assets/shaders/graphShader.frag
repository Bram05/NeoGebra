#version 430 core

out vec4 colour;

in vec2 TexCoords;

uniform vec4 u_Colour;
uniform sampler2D tex;

uniform int u_KernelSize;
uniform int u_Kernel[7][7];
	
void main()
{   
	colour = vec4(1.0,1.0,1.0,1.0) * texture(tex, TexCoords).r * u_Kernel[0][0];

    for (int x = 0; x < u_KernelSize; x++) {
        for (int y = 0; y < u_KernelSize; y++) {
            vec2 coord = TexCoords + vec2(x - int(u_KernelSize/2), y - int(u_KernelSize/2) ) / vec2(textureSize(tex,0));

            colour += texture(tex, coord).r * u_Kernel[x][y];
        }
    }

	colour = min(colour, 1.0);
	colour *= u_Colour;

	//colour = vec4(texture(tex, TexCoords).r, 0.0,0.0,texture(tex, TexCoords).r);

}